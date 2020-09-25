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
    , txData :: Word32
    , rxData :: Word32
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
    | TxData
    | RxData
    | DmaCtl
    | DmaBlk
    | TxFifo
    | RxFifo
    | SpareCtl
    deriving (Show, Eq, Enum)

type SysState a = a

data SpiSlaveCfg = SpiSlaveCfg 
    { id :: Int
    , speedHz :: Word64
    , nssUdelay :: Word32
    , fbDelay :: Word32
    } deriving (Show)

data SpiCsState = SpiCsAssert | SpiCsRelax deriving (Enum)

type CsFn a = SpiSlaveCfg -> Int -> State (SysState a) () 

data SpiBus a b = SpiBus 
    { regs :: SpiRegs
    , clockMode :: Word32
    , inProgress :: Bool
    , txBuffer :: DS.Seq Word8
    , rxBuffer :: DS.Seq Word8  -- can be empty
    , rxSize :: Int
    , chipSelection :: Maybe (CsFn a)
    , callBack :: SpiBus a b -> Int -> b -> State (SysState a) ()
    , token :: b
    , currSlave :: SpiSlaveCfg
    }
{- In Cogent, the SpiBus structure should not be abstract. However,
 - the internal fields can be. This is because we want to implement
 - as much of the code in Cogent rather than in C. If we hide the
 - internal structure, then this removes most of what Cogent can
 - be used for in the SPI driver.
 -
 - Note that the internals of the SpiBus structure is only visible
 - to the functions in "spi.c". Since we will be implementing most
 - of the functionality of "spi.c" except for initialisation, we
 - can arbitrary decide how to represent the structure in Cogent.
 -}

-- #defines
spiXferStsRdy :: Word32
spiXferStsRdy = setBit 0 30

spiCmd1Go :: Word32
spiCmd1Go = setBit 0 31

spiFifoStsRxFifoFlush :: Word32
spiFifoStsRxFifoFlush = setBit 0 15

spiFifoStsTxFifoFlush :: Word32
spiFifoStsTxFifoFlush = setBit 0 14

fifoSize :: Int
fifoSize = 64


-- "FFI" for getting and setting registers
getRegister :: SpiRegs -> SpiRegsField -> (SpiRegs, Word32)
getRegister r Command1 = (r, command1 r)
getRegister r Command2 = (r, command2 r)
getRegister r Timing1 = (r, timing1 r)
getRegister r Timing2 = (r, timing2 r)
getRegister r XferStatus = (r, xferStatus r)
getRegister r FifoStatus = (r, fifoStatus r)
getRegister r TxData = (r, txData r)
getRegister r RxData = (r, rxData r)
getRegister r DmaCtl = (r, dmaCtl r)
getRegister r DmaBlk = (r, dmaBlk r)
getRegister r TxFifo = (r, txFifo r)
getRegister r RxFifo = (r, rxFifo r)
getRegister r SpareCtl = (r, spareCtl r)

putRegister :: SpiRegs -> SpiRegsField -> Word32 -> SpiRegs
putRegister r Command1 x = r { command1 = x}
putRegister r Command2 x = r { command2 = x}
putRegister r Timing1 x = r { timing1 = x }
putRegister r Timing2 x = r { timing2 = x }
putRegister r XferStatus x = r { xferStatus = x }
putRegister r FifoStatus x = r { fifoStatus = x }
putRegister r TxData x = r { txData = x}
putRegister r RxData x = r { rxData = x }
putRegister r DmaCtl x = r { dmaCtl = x }
putRegister r DmaBlk x = r { dmaBlk = x }
putRegister r TxFifo x = r { txFifo = x }
putRegister r RxFifo x = r { rxFifo = x }
putRegister r SpareCtl x = r { spareCtl = x }

-- Haskell prototype

{- Read or flush the rxFifo queue and update the rxBuffer if present.
 -
 - There are two ways to implement this in Cogent.
 -      1) Use the abstract seq32 function to handle the iteration
 -      2) Turn the function into a combination of fold and mapAccum
 -
 -  If we choose 1) then we will need to verify the abstract function
 -  seq32 and possibly its variants. This function is quite useful for
 -  systems code so it should have uses else where (possibly in Bilby
 -  and Ext2).
 -
 -  If we choose 2) then we only need to verify mapAccum since fold
 -  has already been verified (mostly).
 -
 -  Note that fold and mapAccum can be implemented using seq32 and its
 -  variants. In-built arrays are not considered at the moment due to
 -  not supporting dynamically sized arrays which these could
 -  potentially be.
 -}
readOrFlushRx 
    :: Int 
    -> Int 
    -> DS.Seq Word8
    -> SpiRegs
    -> (DS.Seq Word8, SpiRegs)
readOrFlushRx i n w0 r0
    | i < n && i >= 0 =
        let (r1, x) = getRegister r0 RxFifo
            y = fromInteger $ toInteger $ x .&. 0xff
            w1 = DS.update i y w0
        in readOrFlushRx (i+1) n w1 r1
    | otherwise = (w0, r0)

{- Read or flush the rxFifo queue and store the data in the rxBuffer
 - then signal the hardware and indicate the SPI transfer and finished
 - and then run the given callback function.
 -
 - This function is declared as static so it is only called locally.
 -}
finishSpiTransfer :: SpiBus a b -> State (SysState a) ()
finishSpiTransfer s = do
    let size = (DS.length (txBuffer s)) + (rxSize s)
        rxB0 = rxBuffer s
        r0 = regs s
        (rxB1, r1) = readOrFlushRx 0 size rxB0 r0
        (r2, x) = getRegister r1 XferStatus  -- abstract
        r3 = putRegister r2 XferStatus $ x .|. spiXferStsRdy  -- abstract
        s' = s { inProgress = False, rxBuffer = rxB1, regs = r3 }
    maybe (return ()) (\f -> f (currSlave s') (fromEnum SpiCsRelax))
        (chipSelection s')  -- abstract?
    (callBack s') s' size (token s')  -- abstract?

{- Handle IRQ for SPI. If the SPI device is not ready then indicate failure
 - to the user.
 -}
spiHandleIrq :: SpiBus a b -> State (SysState a) ()
spiHandleIrq s = do
    let r0 = regs s
        (r1, xferStat) = getRegister r0 XferStatus  -- abstract
    if (xferStat .&. spiXferStsRdy) /= 0
        then finishSpiTransfer s
        else do
            let (r2, cmd1) = getRegister r1 Command1  -- abstract
                r3 = putRegister r2 Command1 $ cmd1 .&. 
                    (complement spiCmd1Go)  -- abstract
                (r4, fifoStat) = getRegister r3  FifoStatus  -- abstract
                r5 = putRegister r4 FifoStatus $ fifoStat .|. 
                    spiFifoStsRxFifoFlush .|. spiFifoStsTxFifoFlush  -- abstract
                (r6, xferStat') = getRegister r5 XferStatus  -- abstract
                r7 = putRegister r6 XferStatus $ xferStat' .|.
                    spiXferStsRdy  -- abstract
                s' = s { inProgress = False, regs = r7 }
            maybe (return ()) (\f -> f (currSlave s') (fromEnum SpiCsRelax)) 
                (chipSelection s')  -- abstract?
            (callBack s') s' (-1) (token s')  -- abstract?

{- Write the 'txBuffer' to the 'txFifo' queue and then write 
 - @n@ - 'DS.length txBuffer' many 0s to the queue.
 -
 - To implement this, there are two methods:
 -      1) Use seq32.
 -      2) Use fold on the 'txBuffer' and on the 'rxBuffer' for the
 -      remaining amount.
 -
 -  Option 2) involves folding over the 'rxBuffer'. This is only necessary
 -  since Cogent doesn't have iteration over numbers. So option 1) may be
 -  more suitable.
 -}
writeTx :: Int -> Int -> DS.Seq Word8 -> SpiRegs -> SpiRegs
writeTx i n w r0
    | i < n && i >= 0 && i < DS.length w =
        let v = fromInteger $ toInteger $ DS.index w i
            r1 = putRegister r0 TxFifo v  -- abstract
        in writeTx (i+1) n w r1
    | i < n && i >= 0 = 
        let r1 = putRegister r0 TxFifo 0  -- abstract
        in writeTx (i+1) n w r1
    | otherwise = r0


{- Transfer the data in the tx buffer and signal the hardware to
 - handle it.
 -
 - This function is declared as static so it is only called locally.
 -}
startSpiTransfer :: SpiBus a b -> State (SysState a) (SpiBus a b)
startSpiTransfer s = do
    maybe (return ()) (\f -> f (currSlave s) (fromEnum SpiCsAssert)) 
        (chipSelection s)  -- abstract?
    let size = (DS.length (txBuffer s)) + (rxSize s)
        r0 = regs s
        r1 = putRegister r0 DmaBlk $ fromIntegral $ size - 1  -- abstract
        tx = txBuffer s
        r2 = writeTx 0 size tx r1  -- abstract?
        (r3, cmd1) = getRegister r2 Command1  -- abstract
        r4 = putRegister r3 Command1 $ cmd1 .|. spiCmd1Go  -- abstract
    return $ s { regs = r4 }

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
    -> DS.Seq Word8
    -> Int
    -> Maybe (SpiBus a b -> Int -> b -> State (SysState a) ())
    -> b
    -> State (SysState a) (Int, SpiBus a b)
spiXfer s txB rxB rxS cb tok
    | inProgress s = return (-1, s)
    | DS.length txB + rxS > fifoSize = return (-2, s)
    | isNothing cb = return (-3, s)
    | otherwise = do
        let s' = s { txBuffer = txB, rxBuffer = rxB, rxSize = rxS,
            callBack = fromJust cb, token = tok}
        s'' <- startSpiTransfer s'
        return (0, s'')

{- Chooses the slave to interface with. Note that this does not model the
 - multiple slave interfacing since this has not been implemented in the
 - original C source
 -}
spiPrepareTransfer :: SpiBus a b -> SpiSlaveCfg -> SpiBus a b
spiPrepareTransfer s slave = s { currSlave = slave }
