
# a script to rename a file and all href links in html documents
# located in the given directory to this file

# Usage: post_process_docs.pl <directory> <file-pattern>+

# a file_pattern looks like:
# '<old-file-name>:<new-file-name>'

use strict;
use diagnostics;

&usage if @ARGV < 2;

my $dir = shift @ARGV;
my @rules = map {[(split /:/o, $_)[0,1]]} @ARGV;

# print join("\n", map { join("->",@$_); } @rules),"\n";

my @html_files = &read_dir($dir);

# print join(" ", @html_files),"\n";

&move_files;

# reread directory to reflect the movement of files
@html_files = &read_dir($dir);

&rename_links;

########
# subs #
########

sub usage {
print 
'Usage: post_process_docs.pl <directory> <file-pattern>+

 a file_pattern looks like:
 <old-file-name>:<new-file-name>
';
    exit 4;
}

sub read_dir {
    my $dir = $_[0];
    opendir(DOCS_DIR, $dir) or die "cannot open directory for reading $dir";
    my @html_files = grep {$_ = "$dir/$_"; m/\.html$/o} (readdir DOCS_DIR);
    closedir(DOCS_DIR);
    return @html_files;
}

sub move_files {
    foreach my $rule (@rules) {
	my ($old_name,$new_name) = @$rule;
	if (grep(m/$old_name/, @html_files)) {
	    rename "$dir/$old_name", "$dir/$new_name" or
		die "renaming of $old_name failed \n because of: $!";
	}
    } 
}

sub rename_links {
    foreach my $file_name (@html_files) {
	open HTML, "<$file_name" or die "cannot read file $file_name";
	my $file_contents = join "", (<HTML>);
	close HTML;
	my $changed = -42;
	foreach my $rule (@rules) {
	    my ($old_name,$new_name) = @$rule;
	    $changed = ($file_contents =~ s:$old_name:$new_name:gs);
	}
	if ($changed > 0) {
	    open HTML, ">$file_name" or die "cannot write file $file_name";
	    print HTML $file_contents;
	    print STDERR "$file_name modified\n";
	    close HTML;
	}
    }
}
