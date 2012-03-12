#!/usr/bin/perl -w

use strict;
use warnings;
use POSIX qw(strftime);

#my $domain_name = shift(@ARGV);
#my @domain_names = ("satellite", "gripper", "blocksworld");
my @domain_names = ("driverlog", "satellite", "zeno", "gripper", "rovers", "storage", "depots", "blocksworld");
#my @domain_names = ("big_blocksworld", "big_satellite", "big_zeno", "big_driverlog");
#my @domain_names = ("scalable_driverlog", "scalable_zeno");
#my $from_problem_count = shift(@ARGV);
#my $problem_count = shift(@ARGV);

open (TEMP_FILE, '>tmp_plot');
print TEMP_FILE "set title \"Compress rate to time difference.\"\n";
print TEMP_FILE "set xrange [0:100]\n";
print TEMP_FILE "set term postscript enhanced colour\n";
print TEMP_FILE "set output \"simple_compress.ps\"\n";
print TEMP_FILE "set datafile missing \"?\"\n";
print TEMP_FILE "set ylabel \"Relative time difference\"\n";
print TEMP_FILE "set format y \"%g%%\"\n";
print TEMP_FILE "set format x \"%g%%\"\n";
print TEMP_FILE "set yrange [-100:100]\n";
print TEMP_FILE "set ytics 10\n";
print TEMP_FILE "set xtics 10\n";
print TEMP_FILE "set xlabel \"Compression rate\"\n";
print TEMP_FILE "set key top right\n";
print TEMP_FILE "plot ";
my $index = 0;
foreach my $domain_name (@domain_names)
{
	if ($index != 0)
	{
		print TEMP_FILE ", ";
	}
	print TEMP_FILE "\"compress_to_delta/${domain_name}.data\" using 1:2 with points title \"${domain_name}\"";
	$index++;
}
print TEMP_FILE ", 0 notitle";
print TEMP_FILE "\n";
close (TEMP_FILE);

`gnuplot tmp_plot`;
`convert -rotate 90 simple_compress.ps simple_compress.pdf`;

