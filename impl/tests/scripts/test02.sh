source ../common/common.sh
set -e
start_test $1 $2

wd=`pwd`

for i in {1..100}
do
	echo "This is file $i." > $wd/f$i.txt
done

for i in {1..100}
do
	md5sum $wd/f$i.txt >> ../$2
done

ls > $wd/list_files.txt
md5sum $wd/list_files.txt >> ../$2
rm *
ls > $wd/list_files.txt
md5sum $wd/list_files.txt >> ../$2
rm $wd/list_files.txt

end_test
