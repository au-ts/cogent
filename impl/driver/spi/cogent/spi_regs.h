#pragma once

#include <utils/arith.h>

typedef struct spi_regs spi_regs_t;

struct spi_regs {
    volatile uint32_t command1;       /* 000:SPI_COMMAND1 register */
    volatile uint32_t command2;       /* 004:SPI_COMMAND2 register */
    volatile uint32_t timing1;        /* 008:SPI_CS_TIM1 register */
    volatile uint32_t timing2;        /* 00c:SPI_CS_TIM2 register */
    volatile uint32_t xfer_status;    /* 010:SPI_TRANS_STATUS register */
    volatile uint32_t fifo_status;    /* 014:SPI_FIFO_STATUS register */
    volatile uint32_t tx_data;        /* 018:SPI_TX_DATA register */
    volatile uint32_t rx_data;        /* 01c:SPI_RX_DATA register */
    volatile uint32_t dma_ctl;        /* 020:SPI_DMA_CTL register */
    volatile uint32_t dma_blk;        /* 024:SPI_DMA_BLK register */
    PAD_STRUCT_BETWEEN(0x24, 0x108, uint32_t);
    volatile uint32_t tx_fifo;        /* 108:SPI_FIFO1 register */
    PAD_STRUCT_BETWEEN(0x108, 0x188, uint32_t);
    volatile uint32_t rx_fifo;        /* 188:SPI_FIFO2 register */
    volatile uint32_t spare_ctl;      /* 18c:SPI_SPARE_CTRL register */
};
