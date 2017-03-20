source ../common/common.sh
set -e
start_test $1 $2

wd=`pwd`

mkdir -p $wd/a/aa/aaa/aaaa/aaaaa
cd a
cd aa
cd aaa
cd $wd
ls > $wd/files.txt
md5sum $wd/files.txt >> $wd/../$2
touch $wd/a/aa/aaa/aaaa/aaaaa/blah.txt
ls > $wd/files.txt
md5sum $wd/files.txt >> $wd/../$2
cd a/aa/aaa/aaaa/aaaaa/
ls > $wd/files.txt
md5sum $wd/files.txt >> $wd/../$2
cd $wd
ls > $wd/files.txt
md5sum $wd/files.txt >> $wd/../$2
mkdir -p $wd/b/bb/bbb/bbbb/bbbbb
cp $wd/a/aa/aaa/aaaa/aaaaa/blah.txt $wd/b/bb/bbb/bbbb/bbbbb/try.txt
ls > $wd/files.txt
md5sum $wd/files.txt >> $wd/../$2
md5sum $wd/a/aa/aaa/aaaa/aaaaa/* >> $wd/../$2
md5sum $wd/b/bb/bbb/bbbb/bbbbb/* >> $wd/../$2

mv $wd/a $wd/c
ls > $wd/files.txt
md5sum $wd/files.txt >> $wd/../$2
#md5sum c >> ../$2
#md5sum b >> ../$2

rm -rf $wd/c
rm -rf $wd/b

ls > $wd/files.txt
md5sum $wd/files.txt >> $wd/../$2
rm $wd/*

end_test
