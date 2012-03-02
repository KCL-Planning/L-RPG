#!/usr/bin/perl -w

use strict;
use warnings;
use POSIX qw(strftime);

#my $domain_name = shift(@ARGV);
#my @domain_names = ("satellite", "gripper", "blocksworld");
#my @domain_names = ("depots");
my @domain_names = ("driverlog", "satellite", "zeno", "gripper", "rovers", "storage", "depots", "blocksworld");
#my @domain_names = ("big_blocksworld", "big_satellite", "big_zeno", "big_driverlog");
#my @domain_names = ("scalable_driverlog", "scalable_zeno");
#my $from_problem_count = shift(@ARGV);
#my $problem_count = shift(@ARGV);

open (TEMP_FILE, '>tmp_plot');
print TEMP_FILE "set xrange [0.00001:0.1]\n";
print TEMP_FILE "set yrange [0.00001:0.1]\n";
print TEMP_FILE "set log x\n";
print TEMP_FILE "set size 0.8\n";
print TEMP_FILE "set log y\n";
print TEMP_FILE "set title \"Time to do a single reachability analysis from the initial state.\"\n";
print TEMP_FILE "set ylabel \"Grounded reachability Time (s)\"\n";
print TEMP_FILE "set xlabel \"Lifted reachability Time (s)\"\n";
print TEMP_FILE "set term postscript enhanced colour\n";
print TEMP_FILE "set output \"scatterplot.ps\"\n";
print TEMP_FILE "set datafile missing \"?\"\n";
print TEMP_FILE "plot ";
my $index = 0;
foreach my $domain_name (@domain_names)
{
	if ($index != 0)
	{
		print TEMP_FILE ", ";
	}
	print TEMP_FILE "\"merged_results/${domain_name}.data\" using 1:2 with points title \"${domain_name}\"";
	$index++;
}
print TEMP_FILE ", x with lines notitle";
print TEMP_FILE "\n";
close (TEMP_FILE);

`gnuplot tmp_plot`;
`convert -rotate 90 scatterplot.ps scatterplot.pdf`;

