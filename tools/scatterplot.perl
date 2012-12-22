#!/usr/bin/perl -w

use strict;
use warnings;
use POSIX qw(strftime);

#my $domain_name = shift(@ARGV);
#my @domain_names = ("satellite", "gripper", "blocksworld");
#my @domain_names = ("depots");
my @domain_names = ("driverlog", "satellite", "zeno", "rovers", "storage", "depots", "blocksworld");
#my @domain_names = ("big_blocksworld", "big_satellite", "big_zeno", "big_driverlog");
#my @domain_names = ("scalable_driverlog", "scalable_zeno");
#my $from_problem_count = shift(@ARGV);
#my $problem_count = shift(@ARGV);

open (TEMP_FILE, '>tmp_plot');
print TEMP_FILE "set xrange [0.001:10000000]\n";
print TEMP_FILE "set yrange [0.001:10000000]\n";
#print TEMP_FILE "set xrange [0:250]\n";
#print TEMP_FILE "set yrange [0:250]\n";
print TEMP_FILE "set log x\n";
#print TEMP_FILE "set size 0.8\n";
print TEMP_FILE "set log y\n";
print TEMP_FILE "set title \"States explored.\"\n";
print TEMP_FILE "set ylabel \"FF heuristic\"\n";
print TEMP_FILE "set xlabel \"Lifted RPG heuristic\"\n";
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
	print TEMP_FILE "\"merged_results_fully_lifted/${domain_name}-states.dat\" using 1:2 with points title \"${domain_name}\"";
	$index++;
}
print TEMP_FILE ", x with lines notitle";
print TEMP_FILE "\n";
close (TEMP_FILE);

`gnuplot tmp_plot`;
`convert -rotate 90 scatterplot.ps scatterplot.pdf`;

