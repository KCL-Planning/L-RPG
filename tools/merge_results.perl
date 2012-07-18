#!/usr/bin/perl -w

use strict;
use warnings;

my $from_problem_count = shift(@ARGV);
my $problem_count = shift(@ARGV);
my $output_directory = "merged_results";

system ("mkdir -p $output_directory");

opendir(DIR, "latest_heuristics_results/grounded");
my @FILES = readdir(DIR);
closedir(DIR);

foreach my $file (@FILES)
{
	unless ($file =~ m/.*data\Z/) { next; }

	# Find the corresponding file in the lifted directory.
	my $lifted_file_name = "latest_heuristics_results/lifted/".$file;
	if (-e $lifted_file_name)
	{
		print "Found: $lifted_file_name!\n";
	} else {
		print "Could not find: $lifted_file_name - skipping!\n";
		next;
	}

	# Get the 2nd column of every row in each file and concatenate them in a single file.
	open OUTPUT, ">", $output_directory."/".$file;
	open GROUNDED_RESULT, "<", "latest_heuristics_results/grounded/$file" or die $!;
	open LIFTED_RESULT, "<", $lifted_file_name or die $!;

	my @grounded_lines = <GROUNDED_RESULT>;
	my @lifted_lines = <LIFTED_RESULT>;

	unless (scalar (@grounded_lines) eq scalar (@lifted_lines) )
	{
		print "$file The number of data points are not equal ".scalar (@grounded_lines)." v.s. ".scalar (@lifted_lines)."!\n";
		exit;
	}

	for (my $i = 0; $i < scalar (@grounded_lines); $i++)
	{
		my $grounded_line = $grounded_lines[$i];
		my $lifted_line = $lifted_lines[$i];

		# Get the 2nd column of both lines.
		my @grounded_columns = split(' ', $grounded_line);
		my @lifted_columns = split(' ', $lifted_line);

		print OUTPUT "$grounded_columns[1] $lifted_columns[1]\n";
	}

	close OUTPUT;
	close GROUNDED_RESULT;
	close LIFTED_RESULT;
}

