#!/usr/bin/perl -w

use strict;
use warnings;

my $from_problem_count = shift(@ARGV);
my $problem_count = shift(@ARGV);
my $marvin_directory = "/home/bram/projects/marvin-bram/latest_results";
#my $marvin_directory = "/home/bram/projects/marvin-bram/results";
#my $marvin_directory = "/home/bram/projects/MyPOP/tags/ICAPS-2012-speed-1.0/trunk/latest_results";
my $output_directory = "compress_to_delta";

system ("mkdir -p $output_directory");

opendir(DIR, "latest_results");
my @FILES = readdir(DIR);
closedir(DIR);

foreach my $file (@FILES)
{
	unless ($file =~ m/.*data\Z/) { next; }

	# Find the corresponding file in the marvin directory.
	my $marvin_file_name = $marvin_directory."/".$file;
	if (-e $marvin_file_name)
	{
		print "Found: $marvin_file_name!\n";
	} else {
		print "Could not find: $marvin_file_name - skipping!\n";
		next;
	}

	# Get the 2nd column of every row in each file and concatenate them in a single file.
	open OUTPUT, ">", $output_directory."/".$file;
	open LOLLIPOP_RESULT, "<", "latest_results/$file" or die $!;
	open MARVIN_RESULT, "<", $marvin_file_name or die $!;

	my @lollipop_lines = <LOLLIPOP_RESULT>;
	my @marvin_lines = <MARVIN_RESULT>;

	# Combine these with the compression rates.
	open COMPRESSION_RATES, "<", "compression_rates/$file" or die $!;
	my @compression_rates = <COMPRESSION_RATES>;

	unless (scalar (@lollipop_lines) eq scalar (@marvin_lines) and scalar (@compression_rates) eq scalar (@lollipop_lines) )
	{
		print "$file The number of data points are not equal ".scalar (@lollipop_lines)." v.s. ".scalar (@marvin_lines)." v.s. ".scalar (@compression_rates)."!\n";
		next;
	}

	for (my $i = 0; $i < scalar (@lollipop_lines); $i++)
	{
		my $lollipop_line = $lollipop_lines[$i];
		my $marvin_line = $marvin_lines[$i];
		my $compression_rate = $compression_rates[$i];

		# Get the 2nd column of both lines.
		my @lollipop_columns = split(' ', $lollipop_line);
		my @marvin_columns = split(' ', $marvin_line);

		my $l_time = $lollipop_columns[1];
		my $m_time = $marvin_columns[1];

		my $delta = 0;

		if ($l_time < $m_time)
		{
			$delta = ($m_time - $l_time) / $m_time;
		}
		elsif ($l_time > $m_time)
		{
			$delta = -($l_time - $m_time) / $l_time;
		}
		else
		{
			$delta = 0;
		}
		$delta *= 100;
		print OUTPUT substr($compression_rate, 0, -1)." $delta\n";
#		my $time_difference = $marvin_columns[1] - $lollipop_columns[1];

#		print OUTPUT substr($compression_rate, 0, -1)." $time_difference\n";
	}

	close OUTPUT;
	close LOLLIPOP_RESULT;
	close COMPRESSION_RATES;
	close MARVIN_RESULT;
}
