#!/usr/bin/perl -w

use strict;
use warnings;
use POSIX qw(strftime);

#my $domain_name = shift(@ARGV);
#my @domain_names = ("scalable_storage");
my @domain_names = ("airport", "mystery");
#my @domain_names = ("driverlog", "satellite", "zeno", "gripper", "rovers", "storage", "depots", "blocksworld");
#my @domain_names = ("big_storage", "big_driverlog", "big_depots", "big_satellite", "big_zeno");
#my @domain_names = ("big_storage", "big_depots");
my $from_problem_count = shift(@ARGV);
my $problem_count = shift(@ARGV);

my $now = strftime "%Y_%m_%d-%H:%M:%S", localtime;

my $output_path = "results-at-$now";
    
system ("mkdir -p $output_path");
system ("mkdir -p latest_results");

foreach my $domain_name (@domain_names)
{
	my $example_path = "/home/bram/projects/domains/$domain_name";
	print "$domain_name . $from_problem_count . $problem_count";
	print $domain_name."\n";

	`rm $output_path/${domain_name}.data`;
	    
	for (my $i = $from_problem_count, my $j = 0; $i <= $problem_count; $i++, $j++)
	{
		my $count;
		if ($i < 10)
		{
			$count = "0".$i;
		}
		else
		{
			$count = $i;
		}
	#	print $count . "\n";

		my $stuff = `./mypop -val $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1`;
		if ($? != 0)
		{
			print "Failed validation on $domain_name problem number $count!\n";
			next;
		}

		#do planning
		my $total_time = 0;
		my $nr_iterations = 10;
		for (my $i = 0; $i < $nr_iterations; $i++)
		{
#			my $time = substr(`./mypop $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | grep "Reachability analysis" | awk '{print \$3}'`, 0, -1);
			$total_time += substr(`./mypop $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | grep "Reachability analysis" | awk '{print \$3}'`, 0, -1);
		}
		my $time = $total_time / $nr_iterations;
		print "$count - $time\n";
		`echo "$count $time" >> $output_path/${domain_name}.data`;
		`cp $output_path/${domain_name}.data latest_results/${domain_name}.data`;
	}
}
