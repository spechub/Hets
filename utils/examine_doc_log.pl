

# a perl script to examine the output of 'make apache_doc'

# upon a successful run it does nothing
# upon an error it sends an email to the specified address
#
# sample crontab for generating the hets online documentation:
#
# PATH=$PATH:/home/linux-bkb/bin:/usr/bin:/bin
# 43 2 * * *      (cd /home.local/luettich/HetCATS ; time make apache_doc) > /home.local/luettich/HetCATS/make_apache_doc.log 2>&1
# 2 3 * * *       /usr/bin/perl /home.local/luettich/HetCATS/utils/examine_doc_log.pl /home.local/luettich/HetCATS/make_apache_doc.log 'luettich@tzi.de' > /dev/null 2>&1
#
#
#
# Usage: examine_doc_log.pl /path/to/log_file 'luettich@tzi.de'

use strict;

exit 5 if @ARGV < 2;

my ($logfile,$email_address) = @ARGV;
print STDERR "read: $logfile\nmailto: $email_address\n";
my ($report,$fail) = ('',0);

open LOG_FILE, "<$logfile" or 
do { 
    $report .= "cannot read logfile \'$logfile\'!\n$!\n";
    $fail +=1;
};
my %test_vars = ();

if ($fail == 0) {
    while(<LOG_FILE>) {
	# some lines are not relevant
	next if m/^\?|ghc -M/o;
	# do some Tests
	# prepare ghc error
	m/^Compiling|ghc.*?: chasing/o &&
	    do { $test_vars{'ghc_started'}++; };
	# error in Makefile or ghc
	m/^Error: Couldn't create sources/o && # '
	    do {
		if (not exists $test_vars{'ghc_started'}) {
		    # Makefile
		    $report .= 
			"Something strange happend during ".
			"creation of sources_hetcats.mk\n";
		} else {
		    # ghc
		    $report .=
			"An error during compiling 'hets' occured.\n";
		}
		    $fail ++;
	    };
	# haddock error
	m/^([^:]*?):([0-9]+):([0-9]+): Parse error/o &&
	    do {
		$fail ++;
		$report .= "haddock cannot parse $1 at line $2 char $3\n";
	    };
	# lines that should occur
	m/^cvs server:/o && do {$test_vars{'cvs_updated'}++;};
	m/^rm -f /o && do {$test_vars{'cleaning_started'}++;};
	m/^perl utils\/build_version/o && 
	    do {$test_vars{'version build'}++;};
	m/^perl utils\/DrIFT/o && 
	    do {$test_vars{'files drifted'}++;};
	m/^ghc: linking \.\.\.$/o && do {$test_vars{'linking_done'}=1;};
	m/^perl utils\/haddock/o && do {$test_vars{'haddock_started'}=1;};
	m/^perl utils\/post_process_docs.pl/o && 
	    do {$test_vars{'post_process_started'}=1;};
	m/^docs.* modified$/o && do {$test_vars{'modified_lines'}++;};
    }
    close LOG;
    # post process positive lines
    unless (exists $test_vars{'modified_lines'} 
	    && $test_vars{'modified_lines'} > 0) {
	$fail++;
	$report .= "";
    unless (exists $test_vars{'modified_lines'} 
	    && $test_vars{'modified_lines'} > 0) {
	$report .= "no HTML file was modified\n";
	$fail ++;
    }
}

# send report as mail
if ($fail > 0) {
    print STDERR "\n$fail test(s) failed -- sending Mail with report:\n\n$report\n";
    open MAIL, "| /usr/bin/mail -i -n -s 'Error Report of make apache_doc' $email_address";
 print MAIL "$fail tests failed!\n\nSee following report for details:\n\n$report\n";
    close MAIL;
}
