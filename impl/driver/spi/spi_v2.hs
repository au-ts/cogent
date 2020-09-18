--
-- Copyright 2020, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--
-- Prototype of the SPI driver for tk1 from https://github.com/seL4/util_libs
import Data.Word
import Data.Bits
import Data.Maybe
import Control.Monad.State
import qualified Data.Sequence as DS

data SpiRegs = SpiRegs 
    { command1 :: Word32
    , command2 :: Word32
    , timing1 :: Word32
    , timing2 :: Word32
    , xferStatus :: Word32
    , fifoStatus :: Word32
    , dmaCtl :: Word32
    , dmaBlk :: Word32
    , txFifo :: Word32
    , rxFifo :: Word32
    , spareCtl :: Word32
    } deriving (Show)

data SpiRegsField
    = Command1 
    | Command2 
    | Timing1 
    | Timing2 
    | XferStatus
    | FifoStatus
    | DmaCtl
    | DmaBlk
    | TxFifo
    | RxFifo
    | SpareCtl
    deriving (Show, Eq, Enum)

type SysState a = (SpiRegs, a)

type RegsGet a = SpiRegsField -> State (SysState a) Word32
type RegsPut a = SpiRegsField -> Word32 -> State (SysState a) ()

data SpiSlaveCfg = SpiSlaveCfg 
    { id :: Int
    , speedHz :: Word64
    , nssUdelay :: Word32
    , fbDelay :: Word32
    } deriving (Show)

data SpiCsState = SpiCsAssert | SpiCsRelax deriving (Enum)

type CsFn a = SpiSlaveCfg -> Int -> State (SysState a) () 

data SpiBus a b = SpiBus 
    { regsGet :: RegsGet a
    , regsPut :: RegsPut a
    , inProgress :: Bool
    , txBuffer :: DS.Seq Word8
    , txSize :: Int
    , rxBuffer :: Maybe (DS.Seq Word8)
    , rxSize :: Int
    , chipSelection :: Maybe (CsFn a)
    , callBack :: SpiBus a b -> Int -> b -> State (SysState a) ()
    , token :: b
    , currSlave :: SpiSlaveCfg
    }

-- #defines
spiXferStsRdy :: Word32
spiXferStsRdy = setBit 0 39

spiCmd1Go :: Word32
spiCmd1Go = setBit 0 31

spiFifoStsRxFifoFlush :: Word32
spiFifoStsRxFifoFlush = setBit 0 15

spiFifoStsTxFifoFlush :: Word32
spiFifoStsTxFifoFlush = setBit 0 14

fifoSize :: Int
fifoSize = 64

-- Haskell prototype

-- Read or flush the rxFifo queue and update the rxBuffer if present.
readOrFlushRx 
    :: Int 
    -> Int 
    -> SpiBus a b 
    -> State (SysState a) (SpiBus a b)
readOrFlushRx i n s
    | i < n && i >= 0 = do
        x <- (regsGet s) RxFifo
        let xs = rxBuffer s
            y = fromInteger $ toInteger $ x .&. 0xff
            s' = maybe s (\ys -> s { rxBuffer = Just (DS.update i y ys) }) xs
        readOrFlushRx (i+1) n s'
    | otherwise = return s

{- Read or flush the rxFifo queue and store the data in the rxBuffer
 - then signal the hardware and indicate the SPI transfer and finished
 - and then run the given callback function
 -}
finishSpiTransfer :: SpiBus a b -> State (SysState a) ()
finishSpiTransfer s = do
    let size = (txSize s) + (rxSize s)
    s' <- readOrFlushRx 0 size s
    x <- (regsGet s') XferStatus
    (regsPut s') XferStatus $ x .|. spiXferStsRdy
    let s'' = s' { inProgress = False }
    maybe (return ()) (\f -> f (currSlave s'') (fromEnum SpiCsRelax))
        (chipSelection s'')
    (callBack s'') s'' size (token s'')

{- Handle IRQ for SPI. If the SPI device is not ready then indicate failure
 - to the user.
 -}
spiHandleIrq :: SpiBus a b -> State (SysState a) ()
spiHandleIrq s = do
    xferStat <- (regsGet s) XferStatus
    if (xferStat .&. spiXferStsRdy) /= 0
        then finishSpiTransfer s
        else do
            cmd1 <- (regsGet s) Command1
            (regsPut s) Command1 $ cmd1 .&. (complement spiCmd1Go)
            fifoStat <- (regsGet s) FifoStatus
            (regsPut s) FifoStatus $ fifoStat .|. spiFifoStsRxFifoFlush .|.
                spiFifoStsTxFifoFlush
            xferStat' <- (regsGet s) XferStatus
            (regsPut s) XferStatus $ xferStat' .|. spiXferStsRdy
            let s' = s { inProgress = False}
            maybe (return ()) (\f -> f (currSlave s') (fromEnum SpiCsRelax)) 
                (chipSelection s')
            (callBack s') s' (-1) (token s')

{- Write the 'txBuffer' to the 'txFifo' queue and then write @n@ - 'txSize'
 - many 0s to the queue.
 -}
writeTx :: Int -> Int -> SpiBus a b -> State (SysState a) ()
writeTx i n s
    | i < n && i >= 0 && i < DS.length (txBuffer s) && i < txSize s = do
        (regsPut s) TxFifo $ fromInteger $ toInteger $ DS.index (txBuffer s) i
        writeTx (i+1) n s
    | i < n && i >= 0 = do
        (regsPut s) TxFifo 0
        writeTx (i+1) n s
    | otherwise = return ()


{- Transfer the data in the tx buffer and signal the hardware to
 - handle it.
 -}
startSpiTransfer :: SpiBus a b -> State (SysState a) ()
startSpiTransfer s = do
    maybe (return ()) (\f -> f (currSlave s) (fromEnum SpiCsAssert)) 
        (chipSelection s)
    let size = (txSize s) + (rxSize s)
    (regsPut s) DmaBlk $ fromIntegral $ size - 1
    writeTx 0 size s
    cmd1 <- (regsGet s) Command1
    (regsPut s) Command1 $ cmd1 .|. spiCmd1Go

{- Set up the SPI transaction.
 -
 - Not sure that we still want the @c@ argument to be possibly
 - 'Nothing' as this check only occurs in C since pointers can be
 - NULL and synchronous SPI transactions have not been in implemented
 - in the C source.
 -
 - Note that in this prototype the return type is now including the 'SpiBus'
 - datatype. This is so that the size of the 'SysState' is smaller and this
 - models how it would most likely be modelled in Cogent.
 -}
spiXfer
    :: SpiBus a b
    -> DS.Seq Word8
    -> Int
    -> Maybe (DS.Seq Word8)
    -> Int
    -> Maybe (SpiBus a b -> Int -> b -> State (SysState a) ())
    -> b
    -> State (SysState a) (Int, SpiBus a b)
spiXfer s txB txS rxB rxS cb tok
    | inProgress s = return (-1, s)
    | txS + rxS > fifoSize = return (-2, s)
    | isNothing cb = return (-3, s)
    | otherwise = do
        let s' = s { txBuffer = txB, txSize = txS, rxBuffer = rxB, rxSize = rxS,
            callBack = fromJust cb, token = tok}
        startSpiTransfer s'
        return (0, s')

{- Chooses the slave to interface with. Note that this does not model the
 - multiple slave interfacing since this has not been implemented in the
 - original C source
 -}
spiPrepareTransfer :: SpiBus a b -> SpiSlaveCfg -> SpiBus a b
spiPrepareTransfer s slave = s { currSlave = slave }
