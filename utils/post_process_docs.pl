
# a script to rename a file and all href links in html documents
# located in the given directory to this file

# Usage: post_process_docs.pl <directory> <file-pattern>+

# a file_pattern looks like:
# '<old-file-name>:<new-file-name>'

use strict;
use diagnostics;

use File::Find;

&usage if @ARGV < 2;

my $dir = shift @ARGV;
my @rules = map {my @tmp = (split m/:/o, $_)[0,1];$tmp[1] = "" 
		     unless defined $tmp[1];[@tmp]} 
             @ARGV;

print STDERR "Rules:\n",join("\n", map { join("->",@$_); } @rules),"\n\n";

&process2($dir);

########
# subs #
########

sub process2 {
    ## Based on File::Find 
    # maybe a nicer solution
    my $d = $_[0];
    find(\&process2_file, $d);
    return ();
}

sub process2_file {
    # modify file
    &apply_rules($_) if m/\.html$/o;
    # rename file
    foreach my $rule (@rules) {
	my ($old_name,$new_name) = @$rule;
	if (m/^$old_name$/) {
	    rename "$old_name", "$new_name" or
		die "renaming of $old_name failed \n because of: $!";
	}
    }
}

sub usage {
print 
'Usage: post_process_docs.pl <directory> <file-pattern>+

 a file_pattern looks like:
 <old-file-name>:<new-file-name>
';
    exit 4;
}

sub apply_rules {
    my $file_name = $_[0];
    open HTML, "<$file_name" or die "cannot read file $file_name";
    my $file_contents = join "", (<HTML>);
    close HTML;
    my $changed = 0;
    foreach my $rule (@rules) {
	my ($old_name,$new_name) = @$rule;
	$changed += ($file_contents =~ s:$old_name:$new_name:gs);
    }
    if ($changed > 0) {
	open HTML, ">$file_name" or die "cannot write file $file_name";
	print HTML $file_contents;
	print STDERR "$file_name modified\n";
	close HTML;
    }
}

