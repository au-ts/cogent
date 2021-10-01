#!/bin/bash


if [ "$1" = "-clean" ]; then
  umount /mnt/disk
  rmmod cgbilbyfs
  ubidetach -p /dev/mtd0
  exit 0
fi

modprobe nandsim first_id_byte=0xec second_id_byte=0xd3 third_id_byte=0x51 fourth_id_byte=0x95
modprobe ubi
ubiformat /dev/mtd0
ubiattach /dev/ubi_ctrl -m 0
ubimkvol /dev/ubi0 -N bilby -s 956MiB
ubiupdatevol /dev/ubi0_0 -t

insmod cgbilbyfs.ko
mkdir -p /mnt/disk
mount -t bilbyfs ubi0:bilby /mnt/disk
