#!/usr/bin/perl -w

use strict;
use warnings;
use POSIX qw(strftime);

#my $domain_name = shift(@ARGV);
#my @domain_names = ("satellite", "gripper", "blocksworld");
#my @domain_names = ("depots");
my @domain_names = ("driverlog", "satellite", "zeno", "rovers", "storage", "depots", "blocksworld");
my $merged_name = shift(@ARGV);
my $mode = shift(@ARGV);

if ($mode ne "q" and $mode ne "s" and $mode ne "m")
{
	print "Usage perl scatterplot.perl <name of merge director, minus merged_...> <q|s|m>\n";
	exit;
}
#my $merged_name = "all_goals_removed_ff_fully_lifted";
#my @domain_names = ("big_blocksworld", "big_satellite", "big_zeno", "big_driverlog");
#my @domain_names = ("scalable_driverlog", "scalable_zeno");
#my $from_problem_count = shift(@ARGV);
#my $problem_count = shift(@ARGV);

open (TEMP_FILE, '>tmp_plot');
if ($mode eq "q")
{
	print TEMP_FILE "set title \"Plan quality.\"\n";
	print TEMP_FILE "set output \"scatterplot_${merged_name}_pq.ps\"\n";
}
elsif ($mode eq "s")
{
	print TEMP_FILE "set log x\n";
	print TEMP_FILE "set log y\n";
	print TEMP_FILE "set title \"States explored.\"\n";
	print TEMP_FILE "set output \"scatterplot_${merged_name}.ps\"\n";
}
elsif ($mode eq "t")
{
	print TEMP_FILE "set log x\n";
	print TEMP_FILE "set log y\n";
	print TEMP_FILE "set title \"Time (s).\"\n";
	print TEMP_FILE "set output \"scatterplot_${merged_name}_time.ps\"\n";
}
elsif ($mode eq "m")
{
	print TEMP_FILE "set log x\n";
	print TEMP_FILE "set log y\n";
	print TEMP_FILE "set title \"Memory used in bits.\"\n";
	print TEMP_FILE "set output \"scatterplot_${merged_name}_mem.ps\"\n";
}
#print TEMP_FILE "set xrange [1000000:10000000000]\n";
#print TEMP_FILE "set yrange [1000000:10000000000]\n";
#print TEMP_FILE "set xrange [0.001:10000000]\n";
#print TEMP_FILE "set yrange [0.001:10000000]\n";
#print TEMP_FILE "set xrange [1:20]\n";
#print TEMP_FILE "set yrange [0:250]\n";
#print TEMP_FILE "set log x\n";
#print TEMP_FILE "set size 0.8\n";
#print TEMP_FILE "set log y\n";
#print TEMP_FILE "set title \"Memory used in bits.\"\n";
#print TEMP_FILE "set title \"States explored.\"\n";
#print TEMP_FILE "set ylabel \"FF heuristic\"\n";
print TEMP_FILE "set ylabel \"CG heuristic\"\n";
print TEMP_FILE "set xlabel \"Lifted CG heuristic\"\n";
print TEMP_FILE "set term postscript enhanced colour\n";
#print TEMP_FILE "set output \"scatterplot_${merged_name}.ps\"\n";
print TEMP_FILE "set datafile missing \"?\"\n";
print TEMP_FILE "plot ";
my $index = 0;
foreach my $domain_name (@domain_names)
{
	if ($index != 0)
	{
		print TEMP_FILE ", ";
	}
	if ($mode eq "q")
	{
		print TEMP_FILE "\"merged_results_${merged_name}/${domain_name}-quality.dat\" using 1:2 with points title \"${domain_name}\"";
	}
	elsif ($mode eq "s")
	{
		print TEMP_FILE "\"merged_results_${merged_name}/${domain_name}-states.dat\" using 1:2 with points title \"${domain_name}\"";
	}
	elsif ($mode eq "m")
	{
		print TEMP_FILE "\"merged_results_${merged_name}/${domain_name}-memory.dat\" using 1:2 with points title \"${domain_name}\"";
	}
	$index++;
}
print TEMP_FILE ", x with lines notitle";
print TEMP_FILE "\n";
close (TEMP_FILE);

`gnuplot tmp_plot`;

if ($mode eq "q")
{
	`convert -rotate 90 scatterplot_${merged_name}_pq.ps scatterplot_${merged_name}_pq.pdf`;
}
elsif ($mode eq "s")
{
	`convert -rotate 90 scatterplot_${merged_name}.ps scatterplot_${merged_name}.pdf`;
}
elsif ($mode eq "t")
{
	`convert -rotate 90 scatterplot_${merged_name}_time.ps scatterplot_${merged_name}_time.pdf`;
}
elsif ($mode eq "m")
{
	`convert -rotate 90 scatterplot_${merged_name}_mem.ps scatterplot_${merged_name}_mem.pdf`;
}

