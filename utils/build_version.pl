#!/usr/local/bin/perl

# $Id$
# Author: Klaus Lüttich
# Year : 2002

# setting up the Version module for hets

use strict;
use POSIX qw(strftime);

my $currdate = strftime("%d %b %Y",localtime);

my $header = 'This file was generated
     by utils\/build_version.pl
     from Driver\/Version.in
     on ' . $currdate . '!

   Do not edit!';

my $version = "<unknown>";

# check Arguments
if (@ARGV == 1) {
    open VERS,"<".$ARGV[0] or
        die "Coud not open $ARGV[0] for reading";
    $version = join "", <VERS>;
    close VERS;
    $version =~ s/\n//ogs;
    $version = '"v'.$version.', '.$currdate.'"';
} else {
    print STDERR "No version number file given\n";
    exit 5;
}

while (<STDIN>) {
     s/(Version)\.in/\1.hs/o;
     s/>>>HEADER<<</$header/oe;
     s/>>>VERSION<<</$version/oe;
     print;
}
