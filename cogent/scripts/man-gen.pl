#!/usr/bin/perl

use File::Which qw(which);
use warnings qw(all);

#
# Copyright 2017, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

$mandir = $ARGV[0];
$cogent = $ARGV[1];
$manfile = "cogent.1";
$file = "$mandir/$manfile";


system ("which $cogent >/dev/null");
print "Cannot find cogent executable.\n" and die unless (defined $?);

$version = `$cogent -v`;
$version =~ /: (.*)/;
$version = $1;

# print "$version\n";

$date = `date -R`;
$date =~ /^.{3}, (.{11})/;
$date = $1;

# print "$date\n";

$help = `$cogent -h4`;

# print "$help\n";

$synopsis = $help;
$synopsis =~ /^Usage: (.*)/;
$synopsis = $1;

@man_body = split (/\n/, $help);

shift(@man_body);
$man_body = join("\n", @man_body);
$man_body =~ s/^(COMMANDS):/.SH $1/;
$man_body =~ s/\n(FLAGS):/.SH $1/;

$man_head = << "EOF";
.\\" Manpage for Cogent.
.TH man 1 "$date" "$version" "Cogent man page"
.SH NAME
cogent -\\ a compiler for building high-assurance file-systems.
.SH SYNOPSIS
$synopsis
.SH DESCRIPTION
Cogent compiler takes a set of compatible options (actions), with a list of optional flags and an input file.
It is used to compile Cogent source code and generate C code, plus Isabelle/HOL specifications and proofs to
show that the generated C code has the same semantics as the source program (and its shallow HOL embedding).
Cogent compiler comes with an FFI to interact with existing C code. The user needs to write a thin wrapper
in C, with antiquoted Cogent identifiers, in order to access Cogent functions and datatypes. 
EOF


$man_tail = << "EOF";
.SH RESOURCES

* https://ts.data61.csiro.au/projects/TS/cogent.pml

* Source code available at https://github.com/NICTA/cogent

.SH AUTHOR
Trustworthy Systems, Data61
EOF

unlink "$file" if (-e $file);
# print "$file\n";

open($fh, '>>', "$file") or die;
print $fh "$man_head\n\n";
print $fh "$man_body\n\n";
print $fh "$man_tail\n\n";
undef $fh;       # automatically closes the file

