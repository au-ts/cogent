source ../common/common.sh
set -e
start_test $1 $2

wd=`pwd`

ls > $wd/file_list.txt
md5sum $wd/file_list.txt >> $wd/../$2

touch $wd/.....a.txt
touch $wd/a.....txt
touch $wd/a.....
md5sum * >> $wd/../$2
rm $wd/*
rm $wd/...*

ls > $wd/file_list.txt
md5sum $wd/file_list.txt >> $wd/../$2
rm $wd/file_list.txt

end_test
