function start_test {
  cd ..

  if [ -d mountpoint ]; then
    umount mountpoint
    if [ $? -ne 0 ]; then
      echo "Could not unmount mountpoint."
      exit 1
    fi
  fi

  rm -rf mountpoint foo $2
  touch $2
  mkdir mountpoint
  fallocate -l 10M foo
  mkfs.vfat foo > /dev/null
  mount -t $1 -o loop foo mountpoint
  cd mountpoint
}

function end_test {
  cd ..
  umount mountpoint
  if [ $? -ne 0 ]; then
    echo "Could not unmount mountpoint."
    exit 1
  fi
  rm -rf mountpoint foo
}
