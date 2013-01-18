#!/usr/bin/perl -w

use strict;
use warnings;
use POSIX qw(strftime);

#my $domain_name = shift(@ARGV);
#my @domain_names = ("airport", "mystery");
#my @domain_names = ("driverlog", "satellite", "zeno", "gripper", "rovers", "storage", "depots", "blocksworld");
#my @domain_names = ("driverlog");
#my @domain_names = ("big_storage", "big_driverlog", "big_depots", "big_satellite", "big_zeno");
#my @domain_names = ("big_storage", "big_depots");
my $domain_name = shift(@ARGV);
my $from_problem_count = shift(@ARGV);
my $problem_count = shift(@ARGV);

my $now = strftime "%Y_%m_%d-%H:%M:%S", localtime;

#my $output_path = "heuristic-values-at-$now";
my $output_path = "latest_heuristics_results_naive";
    
#system ("mkdir -p $output_path");
system ("mkdir -p $output_path");

#foreach my $domain_name (@domain_names)
{
	my $example_path = "domains/$domain_name";
	print "$domain_name . $from_problem_count . $problem_count";
	print $domain_name."\n";

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

		#do planning
		#my $lifted_output = substr(`ulimit -v 2048000 && ulimit -t 1800 && ./mypop $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | egrep "visited|length"`, 0, -1);
		#my $memory_output = `valgrind --tool=massif --massif-out-file=massif.out ./mypop domains/driverlog/domain.pddl domains/driverlog/pfile01.pddl > result; cat massif.out | grep mem_heap_B | sed -e 's/mem_heap_B=\(.*\)/\1/' | sort -g | tail -n 1`;
#		my $memory_output = `ulimit -v 3000000 && ulimit -t 5400 && valgrind --tool=massif --massif-out-file=massif.out ./mypop -ff $example_path/domain.pddl $example_path/pfile$count.pddl > result; cat massif.out | grep mem_heap_B`;
#		my @memories_recorded = split(/\n/, $memory_output);
#		my $max_memory = 0;
#		foreach my $mem (@memories_recorded)
#		{
#			$mem =~ s/mem_heap_B=//;
#			if ($mem > $max_memory)
#			{
#				$max_memory = $mem;
#			}
#		}
#		print "$max_memory\n";
#		print "Output = $memory_output\n";

		my $lifted_output = substr(`ulimit -v 2048000 && ulimit -t 1800 && ./mypop -ff $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | egrep "visited|length"`, 0, -1);
		my @lifted_lines = split(/\n/, $lifted_output);

		my @lifted_states = split(/ /, $lifted_lines[0]);
		my @lifted_plan_length = split(/ /, $lifted_lines[1]);
		print "$count - Lifted: @lifted_states[2] - Plan length: @lifted_plan_length[2]\n";
		`echo "$count @lifted_states[2]" >> $output_path/${domain_name}-states.dat`;
		`echo "$count @lifted_plan_length[2]" >> $output_path/${domain_name}-quality.dat`;
#		`echo "$count $max_memory" >> latest_heuristics_results/${domain_name}-memory.dat`;
	}
}
