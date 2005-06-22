
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
my @rules = map {my @tmp = (split m/:/o, $_)[0,1];$tmp[1] = "" unless defined $tmp[1];[@tmp]} @ARGV;

print join("\n", map { join("->",@$_); } @rules),"\n";

my @html_files = ();

my @dirs = &process2($dir);

foreach my $d (@dirs) {
    push @dirs, &process($d);
}

########
# subs #
########

sub process {
    my $d = $_[0];
    my %res = &read_dir($d);
    @html_files = @{$res{"html"}};

    print join(" ", @html_files),"\n";

    &move_files;
    
# reread directory to reflect the movement of files
    %res = &read_dir($d);
    @html_files = @{$res{"html"}};
    print join(" ", @html_files),"\n";

    &rename_links;
    @html_files = ();
    return @{$res{"dirs"}};
}

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
	if (m/$old_name/) {
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

sub read_dir {
    my $dir = $_[0];
    opendir(DOCS_DIR, $dir) or die "cannot open directory for reading $dir";
    my @all_files = grep {$_ !~ m,^\.\.?,o } (readdir DOCS_DIR);
    my @html_files = grep {$_ = "$dir/$_"; m/\.html$/o} @all_files;
    my @dirs = grep { -d && -r && -w } @all_files;
    print "Directories: ",join(",", @dirs),"\n";
    closedir(DOCS_DIR);
    return ("html" => \@html_files, "dirs" => \@dirs);
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
	&apply_rules($file_name);
    }
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

