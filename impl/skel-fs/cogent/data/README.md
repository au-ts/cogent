This directory contains two files:

* defns.txt - A file containing a list of Cogent functions that are called from the
              'anti-quoted C'/'C' files.

* types.txt - A file containing a list of external type names to Cogent's C parser.
              This file includes all the types that aren't defined in the .ac files.

The names of the files could be anything, but ensure that the `Makefile`(one level above) reflects those changes in the `DEFNS` and `TYPES` variables.
