#!/usr/bin/env perl
#
# Copyright 2020, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms
# of the GNU General Public License version 2.  Note that NO WARRANTY is
# provided.  See "LICENSE_GPLv2.txt" for details.
#
# @TAG(DATA61_GPL)
#

use strict;
use warnings;

use File::Path qw(make_path);
use File::Which qw(which);
use IO::Handle;
use Time::Piece;

die "usage: $0 <output-dir> <cogent-binary>\n"
  unless scalar @ARGV == 2;

my $output_dir = shift;
my $cogent_bin = shift;
my $filename = 'cogent.1';
my $output_file = $output_dir . '/' . $filename;

make_path $output_dir unless (-d $output_dir);

open my $out, '>', $output_file
	or die "can't write to $output_file: $!";

system "which $cogent_bin >/dev/null";
die "couldn't find Cogent executable" unless defined $?;

my $version = `$cogent_bin -v`;
$version =~ /: (.*)/;
$version = $1;

my $date = localtime->strftime('%B %d, %Y');

$out->print(<<__EOF__ =~ s/\n\n/\n/gmr);
.\\"
.\\" Manual page for Cogent.
.\\"
.\\"
.\\" Copyright 2020, Data61
.\\" Commonwealth Scientific and Industrial Research Organisation (CSIRO)
.\\" ABN 41 687 119 230.
.\\"
.\\" This software may be distributed and modified according to the terms
.\\" of the GNU General Public License version 2.  Note that NO WARRANTY is
.\\" provided.  See "LICENSE_GPLv2.txt" for details.
.\\"
.\\" \@TAG(DATA61_GPL)
.\\"

.Dd $date
.Dt COGENT 1
.Os Data61

.Sh NAME
.Nm cogent
.Nd a compiler for building high-assurance file-systems

.Sh SYNOPSIS
.Nm
.Ar COMMAND...
.Bq Ar FLAG...
.Ar FILENAME

.Sh DESCRIPTION
The
.Nm
compiler takes a set of commands,
with a list of optional flags,
and an input file.
It is used to compile Cogent source code
and generate C code,
plus Isabelle/HOL specifications and proofs
to show that the generated C code
has the same semantics as the source program
(and its shallow HOL embedding).
The
.Nm
compiler supports FFI to interact with existing C code.
The user needs to write a thin wrapper in C,
with antiquoted Cogent identifiers,
in order to access Cogent functions and datatypes.

__EOF__

open my $fh, "$cogent_bin -h4 |"
	or die "couldn't run '$cogent_bin': $!";
while (<$fh>) {
	chomp;

	# Drop the blank line.
	next if $_ eq '';

	# Transform headers.
	$out->print(".Sh $1\n") and next
		if /\A(COMMANDS|FLAGS):\Z/;

	# TODO(jashank): munge options into mandoc format
	$out->print("$_\n");
}
$fh->close;

$out->print(<<__EOF__ =~ s/\n\n/\n/gmr);
.\\" .Sh ENVIRONMENT
.\\" .Sh FILES
.\\" .Sh EXIT STATUS
.\\" .Sh EXAMPLES
.\\" .Sh DIAGNOSTICS

.Sh SEE ALSO
The full documentation for
.Nm
is maintained online.
.Bl -dash -compact
.It
.Lk https://cogent.readthedocs.io/
.It
.Lk https://ts.data61.csiro.au/projects/TS/cogent.pml
.It
.Lk https://github.com/NICTA/cogent
.El

.\\" .Sh STANDARDS

.\\" .Sh HISTORY

.Sh AUTHORS
.An Trustworthy Systems at Data61, CSIRO

.\\" .Sh CAVEATS

.\\" .Sh BUGS

__EOF__

$out->close;
