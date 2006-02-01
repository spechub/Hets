#!/usr/bin/perl

use strict;

my ($passwd,$len,$nletters,$salt,$result) = ("",0,0,"","");

while(1) {
    print("Enter password (THIS WILL BE ECHOED TO YOUR SCREEN).\n");
    $passwd = <STDIN>;
    chomp $passwd;
    $len=length($passwd);
    if(($len>8)||($len<6)) {
	print("Password must be 6, 7 or 8 characters long.\n");
	next;
    }
   
    if($passwd =~ m/^[a-zA-Z]+$/o) {
	print("Password should contain at least one non-letter.\n");
	next;
    }
    print "Foo\n";
    last;
}

print("Enter salt.  This is not secret but should be a random\n",
      "combination of two characters, each of which is an upper\n",
      "or lower case letter, a digit, or . or /.\n");

$salt = <STDIN>;
$result=crypt($passwd,$salt);

if(! defined $result) {
    print("Error in crypt.\n");
} else {
    print("Password is \"$passwd\"\n",
	  "Send the following string: \"$result\".\n");

}
