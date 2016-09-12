#!/bin/bash
#!/bin/bash
#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

if [[ -z $SED ]]; then
  ARCH=`uname`
  if [[ $ARCH == "Darwin" ]]; then
    SED=gsed
  else
    SED=sed
  fi
fi


cogent_opts=$(
cogent --help=4 | egrep -v "^(Usage|Commands|Flags)" | \
egrep -v '^\s*$' | \

while read cmd
do
  echo "$cmd" | $SED -r -e "s/\s\s+/\t/g" | \
  awk -F "\t" -v OFS=, \
  '{ for (i = 1; i <= NF - 1; i++)
     { printf $i", " }
   }'
done | \
awk -F , -v OFS=\n \
'{ for (i = 1; i <= NF -1; i++)
   { printf $i"\n" }
 }' | \
while read cmd
do
  echo $cmd | $SED -r -e "s/^\s+//g" | \
  $SED -r -e "s/\[.*\]//" | \
  $SED -r -e "s/=(.*)$//"
done | \
while read opt
do
  echo -n "$opt "
done
)


# Origin of this function:
#   http://askubuntu.com/questions/68175/how-to-create-script-with-auto-complete

_cogent()
{
  local cur prev opts
  COMPREPLY=()
  cur="${COMP_WORDS[COMP_CWORD]}"
  prev="${COMP_WORDS[COMP_CWORD-1]}"
  opts="$cogent_opts"
  if [[ ${cur} == -* ]] ; then
      COMPREPLY=( $(compgen -W "${opts}" -- ${cur}) )
      return 0
  fi
}

complete -o default -F _cogent cogent
