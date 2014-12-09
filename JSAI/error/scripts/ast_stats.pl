#!/usr/bin/perl

use strict;

# returns the number of notJS nodes over the number of Rhino nodes,
# or undef if there was a parse failure in the translator
sub percentage($) {
    my $filename = shift();
    open(INPUT, "<$filename") or die "Could not open '$filename'";
    my $numRhino = undef;
    my $numNotJS = undef;
    while (my $line = <INPUT>) {
	chomp($line);
	if ($line =~ /Number of Rhino nodes: (\d+)/) {
	    $numRhino = $1;
	} elsif ($line =~ /Number of notJS nodes: (\d+)/) {
	    $numNotJS = $1;
	}
    }
    close(INPUT);
    if ($numRhino && $numNotJS) {
	return $numNotJS / $numRhino;
    } else {
	return undef;
    }
}

if (scalar(@ARGV) > 0) {
    my $sum = 0;
    foreach my $filename (@ARGV) {
	$sum += percentage($filename);
    }
    print "Average notJS / Rhino AST: " . ($sum / scalar(@ARGV)) . "\n";
} else {
    print "Needs files that hold the output of notjs.translator.AstStats\n";
}
