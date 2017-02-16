source ../common/common.sh
set -e
start_test $1 $2

wd=`pwd`

echo "Test text file with data." > $wd/a....
md5sum $wd/a.... >> $wd/../$2
echo "This should be the same file (in VFAT)." > $wd/a
md5sum $wd/a >> $wd/../$2
md5sum $wd/a.... >> $wd/../$2
echo "This is different." > $wd/...a...
md5sum $wd/a >> $wd/../$2
md5sum $wd/a.... >> $wd/../$2
md5sum $wd/...a... >> $wd/../$2
ls > $wd/list_files.txt
md5sum $wd/list_files.txt >> $wd/../$2
rm $wd/...a...
ls > $wd/list_files.txt
md5sum $wd/list_files.txt >> $wd/../$2
rm $wd/*

end_test
