#!/usr/bin/perl -w

use strict;
use warnings;
use POSIX qw(strftime);

#my $domain_name = shift(@ARGV);
#my @domain_names = ("satellite", "gripper", "blocksworld");
my @domain_names = ("driverlog", "satellite", "zeno", "gripper", "rovers", "storage", "depots", "blocksworld");
#my @domain_names = ("big_blocksworld", "big_satellite", "big_zeno", "big_driverlog", "big_storage");
#my @domain_names = ("scalable_driverlog", "scalable_zeno");
#my $from_problem_count = shift(@ARGV);
#my $problem_count = shift(@ARGV);

open (TEMP_FILE, '>tmp_plot');
print TEMP_FILE "set xrange [0:100]\n";
print TEMP_FILE "set term postscript enhanced colour\n";
print TEMP_FILE "set output \"compress.ps\"\n";
print TEMP_FILE "set datafile missing \"?\"\n";

print TEMP_FILE "set multiplot\n";
print TEMP_FILE "set ylabel \"Time difference in percent\" offset 0,7.6\n";
print TEMP_FILE "set yrange [0.001:100] reverse\n";
print TEMP_FILE "set format y \"-%g\"\n";
print TEMP_FILE "set origin 0.0,0.0\n";
print TEMP_FILE "set tmargin 0\n";
print TEMP_FILE "set xlabel \"Compression rate (%)\"\n";
print TEMP_FILE "set size 1,0.5\n";
print TEMP_FILE "set nokey\n";
print TEMP_FILE "plot ";
my $index = 0;
foreach my $domain_name (@domain_names)
{
	if ($index != 0)
	{
		print TEMP_FILE ", ";
	}
#	print TEMP_FILE "\"compress_to_delta/${domain_name}.data\" using 1:2 with points title \"${domain_name}\"";
#	print TEMP_FILE "\"compress_to_delta/${domain_name}.data\" using 1:(\$2>0?\$2:0/0) with points title \"${domain_name}\",";
	print TEMP_FILE "\"compress_to_delta/${domain_name}.data\" using 1:(\$2<0?-\$2:0/0) with points title \"${domain_name}\"";
	$index++;
}
print TEMP_FILE "\n";

print TEMP_FILE "set yrange [0.001:100]\n";
print TEMP_FILE "set origin 0.0,0.5\n";
print TEMP_FILE "set size 1,0.5\n";
print TEMP_FILE "set format x \"\"\n";
print TEMP_FILE "set xlabel \"\"\n";
print TEMP_FILE "set ylabel \" \"\n";
print TEMP_FILE "set format y \" %g\"\n";
print TEMP_FILE "set title \"Compress rate to time difference.\"\n";
print TEMP_FILE "set bmargin 0\n";
print TEMP_FILE "set tmargin 1\n";
print TEMP_FILE "set key top right\n";
print TEMP_FILE "plot ";
$index = 0;
foreach my $domain_name (@domain_names)
{
	if ($index != 0)
	{
		print TEMP_FILE ", ";
	}
	print TEMP_FILE "\"compress_to_delta/${domain_name}.data\" using 1:(\$2>0?\$2:0/0) with points title \"${domain_name}\"";
	$index++;
}
print TEMP_FILE "\n";
print TEMP_FILE "set nomultiplot\n";
print TEMP_FILE "set size 0.8\n";
close (TEMP_FILE);

`gnuplot tmp_plot`;
`convert -rotate 90 compress.ps compress.pdf`;

