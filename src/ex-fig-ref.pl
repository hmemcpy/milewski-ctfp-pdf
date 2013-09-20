#! /usr/bin/perl -w

 ################################################# 
#                                                 #
#  Generates tabulated cross references           #
#  pointing to all exercises or figures in SICP.  #
#  Usage: ./ex-fig-ref.pl -e > exercises.tex      #
#  or ./ex-fig-ref.pl -f > figures.tex            #
#  (both of which will be read in by sicp.tex).   #
#                                                 #
#  © 2013 Andres Raba / License: GNU GPL v.3      #
#                                                 #
 ################################################# 


$columns = 10;		# no. of columns in the table

%ex_per_chap = (	# how many exercises per chapter
	1 => 46,
	2 => 97,
	3 => 82,
	4 => 79,
	5 => 52
);

%fig_per_chap = (	# how many figures per chapter
	1 => 5,
	2 => 26,
	3 => 38,
	4 => 6,
	5 => 18
);

if (defined($ARGV[0]) and $ARGV[0] eq "-e") {
	$reftype = "Exercise";
	%ref_per_chap = %ex_per_chap;

} elsif (defined($ARGV[0]) and $ARGV[0] eq "-f") {
	$reftype = "Figure";
	%ref_per_chap = %fig_per_chap;

} else {
	print "Choose '-e' for list of exercises or '-f' for list of figures.\n";
}

foreach $chap_no (sort keys(%ref_per_chap)) {

	print "\\subsubsection*\{Chapter $chap_no\} \n\n";
	print "\\begin\{tabular\}\{" . 'l' x $columns . "\}\n";

	for ($ref_no = 1; $ref_no <= $ref_per_chap{$chap_no}; $ref_no++) {

		if ($ref_no != 1 and (($ref_no - 1) % $columns) == 0) {
			print "\n\\\\ \n";
		}

		print "\\hyperref[$reftype $chap_no.$ref_no]{$chap_no.$ref_no}";

		if (($ref_no % $columns) != 0) {
			print " \&\n";
		} 
	}

	print "\\end\{tabular\} \n\n";
}
