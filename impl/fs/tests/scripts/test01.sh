source ../common/common.sh
set -e
start_test $1 $2

wd=`pwd`

touch $wd/text_file.txt
md5sum $wd/text_file.txt >> ../$2
rm $wd/text_file.txt

end_test
