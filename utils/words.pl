#!/usr/bin/perl -w

use strict;
use File::Basename;

# ##### old intention below
# read file "words.input" from current directory and produce
# "\wordline{<word>}\hline" lines. plus patterns written in lines
# starting with "%" . THe pattern should contain a variable calles
# "$word. It functions as input.
#  words.input contains words seperated
# by space, newline or tabular creates or overwrites a file called
# "generated-words.tex"

# the fonts file can be created by this bash line:
# for f in `ls /usr/share/texmf/tex/latex/psnfss/*.sty` ; do f=`basename $f| sed 's/\.sty//'`;echo '\usepackage{'$f'} ::: '$f ; done > fonts.input

########
# conf #
########

my $PDFLATEX_BIN = 'pdflatex';
my $PDFTOTEXT_BIN = 'pdftotext';

my $DO_PDFLATEX = 1;  # 1 = do it
my $DO_PDFTOTEXT = 1; # 0 = don't do it

#$ENV{'TEXINPUTS'} =$ENV{'TEXINPUTS'}."::".dirname($0);

my $haskell_header =
'{- |
Module      :  $Header$
Description :  several tables needed for LaTeX formatting
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

{-

    Created by a Perl-script (utils/words.pl)!
    DO NOT MODIFY BY HAND!!

-}

module Common.LaTeX_maps where

import Data.Map (fromList, Map)

';

########
# main #
########

my %used_words = &process_the_words; # the words, LaTeX makros,
                        # syllables (ligatures),  letters widely
                        # used in (Het)CASL
# Split into sections that give the names of the Haskell maps.

my @fonts = &read_fonts; # adds an "empty font" for LaTeX-default
my %widths = (); # a table of width from various fonts

foreach my $font (@fonts) {
   $widths{$font->[1]} = &process_one_font($font);
   # debugging
   0 && do {
       foreach my $sec (keys %{$widths{$font->[1]}}) {
           print "$sec :", join(",", @{${$widths{$font->[1]}}{$sec}}),"\n";
       }
   };
}

my %word_widths = &calc_max_width(\%widths,\%used_words);
         # a table of sections to table of
         # words per section to max width over all fonts

# debugging
1 && do {
    foreach my $sec (keys %word_widths) {
        print "$sec :\n",
        join(", ", (map {"$_: ".$word_widths{$sec}{$_}; }
                        (sort (keys %{$word_widths{$sec}})))),
        "\n";
    }
 };

&generate_haskell_FM(\%word_widths); # uses %word_widths

########
# subs #
########

sub generate_haskell_FM {
    my $word_widths = $_[0];


    open HASKELL, "> LaTeX_maps.hs" or
        die "cannot create Haskell module \"LaTeX_maps.hs\"";
    print HASKELL $haskell_header;

    my @two_letter_words = ();
    foreach my $sec (keys %{$word_widths}) {
        # generate a list of pairs for each section named after the section
        print HASKELL &fm_header($sec);
        my @words = sort (keys %{$word_widths->{$sec}});
        push @two_letter_words, (grep {length($_) == 2;} @words);
        print HASKELL " [",
        join(",", (map {"(\"".&escape_String($_)."\",".
                            int($word_widths->{$sec}{$_} * 0.351 * 1000).
                            ')';
                    }
                     (@words))),
        "]\n";
        print HASKELL &key_fm_header($sec);
        my @long_words = sort (grep {length($_) > 2;} @words);
        my $last_word = '';
        my @first_letters =
            grep {my $ret = $_ ne $last_word;$last_word = $_;$ret; }
                 (sort (map {m/^(.)/o;$1} @long_words));
        print HASKELL " [",
        join(",",map {my $c = &escape_String($_);
                      "('".$c."',[".
                          join(",",map {"\"".
                          &escape_String($_).
                          "\""}
                                (grep {m/^$c/}
                                      @long_words)).
                          "])"} @first_letters), "]\n";
    }
    my $last_word = '';
    print HASKELL "\nligatures :: Map String Bool\n",
    "ligatures = fromList [",
    join(",", map { "(\"".&escape_String($_)."\",True)";}
         grep {my $ret = $_ ne $last_word;$last_word = $_;$ret; }
                (sort @two_letter_words)),
    "]\n";
}

sub escape_String {
    return join("", map {
        if (m/^\\$/o) {
            "\\$_";
        } elsif(m/^"$/o) { # "
            "\\$_";
        } else {
            # substitute ÄÖÜßäöü with \196\214\220\223\228\246\252
            $_ =~ s/Ä/\\196/o; $_ =~ s/Ö/\\214/o; $_ =~ s/Ü/\\220/o;
            $_ =~ s/ß/\\223/o;
            $_ =~ s/ä/\\228/o; $_ =~ s/ö/\\246/o; $_ =~ s/ü/\\252/o;
            $_;
        }
    } split(//o,$_[0]));
}

sub fm_header {
    my $map_name = $_[0]."_map";
    return "\n$map_name :: Map String Int\n$map_name = fromList";
}

sub key_fm_header {
    my $map_name = "key_".$_[0]."_map";
    return "\n$map_name :: Map Char [String]\n$map_name = fromList";
}


sub calc_max_width {
    my $font_widths = $_[0];
    my $words       = $_[1];
    my @fonts = keys %{$font_widths};
    my %max_widths = ();

    foreach my $sec (keys %{$words}) {
        my %word_max_width = ();
        my $width_word_index = 0;
        print "$sec: ";
        foreach my $word (@{$words->{$sec}}) {
            my $max = 0;
            #print "$word: ";
            foreach my $font (@fonts) {
                my $cur = $font_widths->{$font}->{$sec}->[$width_word_index];
                $cur = 0 unless defined $cur;
                $max = &max($max,$cur);
                print "$font: ".int($cur * 0.351 * 1000)." " if $word eq "~";
            }
            print "\n" if $word eq "~";
            print STDERR
                     "\nWarning: max length of $word is undefined or zero\n"
                if ! defined $max || $max == 0;
            $word_max_width{$word} = $max;
            $width_word_index++;
            #exit if $width_word_index >= 5;
        }
        $max_widths{$sec} = \%word_max_width;
        #exit;
    }
    return %max_widths;
}

sub max {
    return (($_[0] >= $_[1]) ? $_[0] : $_[1]);
}

sub process_one_font {
    # debugging: print "font: ".join(", ", @{$_[0]})."\n";
    my ($font_cmnd,$font_name) = @{$_[0]};
    # generate two documents one human readable and one for the machine
    my $computer_tex_filename =
        # &gen_tex('width-table.tex.svmono.templ',
        &gen_tex('width-table.tex.templ',
                 $font_name,'computer',$font_cmnd);
    my $human_tex_filename =
        # &gen_tex('width-table.tex.svmono.templ',
        &gen_tex('width-table.tex.templ',
                 $font_name,'human',$font_cmnd);
    if ($DO_PDFLATEX) {
        &pdflatex($computer_tex_filename);
        &pdflatex($human_tex_filename);
    }
    my $computer_pdf_filename =
        basename($computer_tex_filename,'.tex').'.pdf';
    return &get_widths($computer_pdf_filename); # seperated in sections
}

sub pdflatex {
    my $tex_filename = $_[0];
    system($PDFLATEX_BIN,$tex_filename);
}

sub get_widths {
    my $pdf_filename = $_[0];
    my $txt_filename = basename($pdf_filename,'.pdf').'.txt';
    my %widths = ();
    if ($DO_PDFTOTEXT) {
        system($PDFTOTEXT_BIN,"-raw",$pdf_filename);
    }
    #open WIDTH, "pdftotext $pdf_filename | egrep 'section: |wl: ' |"
#       or die "cannot call pdftotext or egrep or cannot fork";
    open WIDTH, "< $txt_filename"
        or die "cannot read file \"$txt_filename\"";
    my $section = '';
    my @widths = ();
    while (<WIDTH>) {
        m/section: (\w+)\+\+\+/o && do {
            unless ($section eq '') {
                $widths{$section} = [@widths];
                @widths = ();
            }
            $section = $1;
        };
        m/wl: (\d+\.\d+)pt/o && $section ne '' && do {
            push @widths, $1;
        };
    }
    close WIDTH;
    $widths{$section} = [@widths];
    # debugging
    0 && do {
        foreach my $sec (keys %widths) {
            print "$sec :", join(",", @{$widths{$sec}}),"\n";
        }
   };
    return \%widths;
}

sub gen_tex {
    my ($input_filename,$font_name,$purpose,$font_cmnd) = @_;
    my $output_filename =
        basename($input_filename,'.tex.templ').".$font_name.".
        substr($purpose,0,1).".tex";
    my $no_cols = '';
    open TEMPL, "< $input_filename";
    open OUT,   "> $output_filename";
    $purpose eq 'human' && do {$no_cols = '';};
    $purpose eq 'computer' && do {$no_cols = '% ';};
    while (<TEMPL>) {
        s/<set-font>/$font_cmnd/;
        s/<no-columns>/$no_cols/;
        print OUT $_;
    }
    close TEMPL;
    close OUT;
    return $output_filename;
}

sub read_fonts {
    open FONTS, "< fonts.input"
        or die "cannot open file \"fonts.input\" for reading";
    my @read_fonts = ();
    while (<FONTS>) {
        chomp;
        my @fnt_descrp = split /\s+:::\s+/;
        push @read_fonts, \@fnt_descrp;
    }
    close FONTS;
    unshift @read_fonts, [('','default')];
    return @read_fonts;
}

my $count_words = 0;
sub process_the_words {
    my $pat = '%s';
    my $line = '';
    my @sec_words = ();
    my %all_words = ();
    my $section = '';

    open WORDS, "< words.input" or die("no file named \"words.input\" found");
    open GENWORDS, "> generated_words.tex"
        or die "cannot write to file \"generated_words.tex\"!";
    while ($line = <WORDS>) {
        &sep_tabular,next if $line=~ m/^\s*$/o;
        if ($line =~ m/^%/o) {
            chomp $line;
            if ($line =~ m/^\%pattern:\s*/o) {
                $line =~ s///o;
                $pat = $line;
            } elsif ($line =~ m/^%section:\s*/o) {
                #print STDERR "$section : ",join(", ",@sec_words),"\n";
                unless ($section eq '') {
                    $all_words{$section} = [@sec_words];
                    #print STDERR "pushed: $section : ",join(", ",@sec_words),"\n";
                }
                @sec_words = ();
                $line =~ s///o;
                $section = $line;
                &sep_tabular("\\newpage\n\\section*{section: $section+++}\n");
            } else {
                print STDERR "unknown directive: $line\n";
            }
        } elsif ($line =~ m/^&/o) {
            $line =~ s///o;
            print GENWORDS $line;
        } elsif ($line =~ m/^~(.*)$/o) {
            &sep_tabular($1);
        } else {
            my @words = split(/\s+/o, $line);
            push @sec_words, @words;
            foreach my $word (@words) {
                my $fpat= sprintf($pat,$word);
                print GENWORDS "\\wordline{$fpat}\n\\hline\n";
                if(++$count_words >= 37) {
                    &sep_tabular;
                }
            }
        }
    }
    close WORDS;
    close GENWORDS;
    $all_words{$section} = [@sec_words];
    return %all_words;
}

sub sep_tabular {
    my $fill_in = defined $_[0] ? $_[0] : '';
    $count_words = 0;
    print GENWORDS "\\end{tabular}\n$fill_in\n\\begin{tabular}{l|l}\n\\hline\n";
}
