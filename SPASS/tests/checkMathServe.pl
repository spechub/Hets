#!/usr/bin/perl

# use this script for the cron-job that checks for a running MathServe 
# on the default server. It also restarts the server with the script given as
# first argument.

# the crontab should look like this:
# PATH=$PATH:/usr/bin:/bin
# 30 0 * * *      /usr/bin/perl /home.local/luettich/HDocs/HetCATS/utils/update_central_CASL-lib.pl /local/home/luettich/mathServ/restart.sh 'luettich@tzi.de' <more email addresses could follow>

use strict;

my $DEBUG = 0; # if set to > 0 no Mail is generated
               # if set to 0 no messages go to STDERR
# close STDERR
close STDERR unless $DEBUG;


if(@ARGV < 2) {
    print STDERR "provide script and at least one email address!!\n"; 
    exit 5;
}

my $restart_script = shift @ARGV;
my $email_address = join(" ",@ARGV);

## config
my $run_dir = "/Users/luettich/CASL/HetCATS/SPASS/tests";
my $stderr_log_file = "/tmp/checkMathServe_errors.log";

# status variable
my $fail = 0;

# issue cvs cmd in the directory
my $log = `cd $run_dir; ./CMDL_tests fast 2> $stderr_log_file`;
my $ret_val = $? >> 8;

print STDERR $log,"\nExitcode: $ret_val\n";

# check the exit value
if($ret_val) {
    $fail++;
    open SLOG, "<$stderr_log_file" or die "recently written $stderr_log_file was lost";
    $log .= "\nMessages to STDERR:\n".join("",<SLOG>);
    close SLOG;
}

# send report as mail and execute restart_script with /bin/sh
if ($fail > 0) {
    print STDERR "\n./CMDL_tests returned with exit code $ret_val -- sending Mail with this log-message:\n\n$log\n";
    unless ($DEBUG) {
	open MAIL, "| /usr/bin/mail -i -n -s 'Error Report of MathServe test' $email_address";
	print MAIL "'CMDL_tests fast' failed with exit code $ret_val!\n\nSee following report for details:\n\n$log\n";
	close MAIL;
    }
    exec "/bin/sh $restart_script";
}
