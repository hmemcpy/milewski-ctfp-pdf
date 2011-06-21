#! /usr/bin/perl

############################################################################
#  Generates tabulated cross references pointing to all exercises in SICP  #
#  Usage: ./exref.pl > exercises.texi (which is @included by sicp.texi)    #
#                                                                          #
#  © 2011 Andres Raba / License: Creative Commons Attribution (CC BY 3.0)  #
############################################################################

use Math::BigFloat;

$columns = 12;		# no. of columns in the table
$squeeze = 0.70;	# decrease first column width 
$reftype = "Exercise";

%ex_per_chap = (	# how many exercises per chapter
	1 => 46,
	2 => 97,
	3 => 82,
	4 => 79,
	5 => 52
);

foreach $chap_no (sort keys(%ex_per_chap)) {

	print "\@subsubheading Chapter $chap_no \n\n";
	print "\@multitable \@columnfractions ";

	$frac = Math::BigFloat->new(1.0 / $columns);
	# each column as a fraction of page width

	$roundfrac = $frac->fround(2);		
	# is there a simpler way to round?

	print $squeeze * $roundfrac, " ";
	for ($i = 2; $i <= $columns; $i++) {
		print "$roundfrac ";
	}
	print "\n";

	for ($ex_no = 1; $ex_no <= $ex_per_chap{$chap_no}; $ex_no++) {	

		if (($ex_no == 1) || ((($ex_no - 1) % $columns) == 0)) {
			print "\@item \n";
		}

		print "\@ref{$reftype $chap_no.$ex_no,,$chap_no.$ex_no}";

		if (($ex_no % $columns) != 0) {
			print " \@tab \n";
		} 
		else {
			print "\n";
		}
	}

	print "\@end multitable \n\n";
}


