#!/usr/bin/perl

# use this script for the cron-job that updates nightly the central
# CASL-lib directory from the CVS Server.

# The Path to the directory is /home/cofi/CASL-lib and is checked out
# with cvsread. So it might be overtaken by another cofi-person
# easily.

# the crontab should look like this:
# PATH=$PATH:/home/linux-bkb/bin:/usr/bin:/bin
# 30 0 * * *      /usr/bin/perl /home.local/luettich/HDocs/HetCATS/utils/update_central_CASL-lib.pl 'luettich@tzi.de' <more email addresses could follow>

use strict;

my $DEBUG = 0; # if set to > 0 no Mail is generated
               # if set to 0 no messages go to STDERR
# close STDERR
close STDERR unless $DEBUG;


if(@ARGV < 1) {
    print STDERR "no email address given!!\n"; 
    exit 5;
}

my $email_address = join(" ",@ARGV);

## config
my $cvs_dir = "/home/cofi/CASL-lib";
my $stderr_log_file = "/tmp/CASL-lib-cvs-up.log";

# status variable
my $fail = 0;

# issue cvs cmd in the directory
my $log = `cd $cvs_dir; /usr/bin/cvs up -Pd 2> $stderr_log_file`;
my $ret_val = $? >> 8;

print STDERR $log,"\nExitcode: $ret_val\n";

# check the exit value
if($ret_val) {
    $fail++;
    open SLOG, "<$stderr_log_file" or die "recently written $stderr_log_file was lost";
    $log .= "\nMessages to STDERR:\n".join("",<SLOG>);
    close SLOG;
}

# send report as mail
if ($fail > 0) {
    print STDERR "\nCVS returned with exit code $ret_val -- sending Mail with this log-message:\n\n$log\n";
    unless ($DEBUG) {
	open MAIL, "| /usr/bin/mail -i -n -s 'Error Report of CVS update /.../CASL-lib' $email_address";
	print MAIL "CVS failed with exit code $ret_val!\n\nSee following report for details:\n\n$log\n";
	close MAIL;
    }
}
