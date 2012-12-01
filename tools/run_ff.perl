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

my $output_path = "heuristic-values-at-$now";
    
system ("mkdir -p $output_path");
system ("mkdir -p latest_heuristics_results");

#foreach my $domain_name (@domain_names)
{
	#my $example_path = "/home/bram/projects/domains/$domain_name";
	my $example_path = "domains/$domain_name";
	print "$domain_name . $from_problem_count . $problem_count";
	print $domain_name."\n";

#	`rm $output_path/${domain_name}.data`;
	    
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

		#do planning
#		my $ff_output = substr(`ulimit -t 600 && ./mypop -g $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | egrep "visited|length"`, 0, -1);
#		my @ff_lines = split(/\n/, $ff_output);
#		my $ff_plan_valid = `VALfiles/validate $example_path/domain.pddl $example_path/pfile$count.pddl solution-$domain_name-pfile$count | grep "Plan valid"`;
#		if (length($ff_plan_valid) lt 1)
#		{
#			print "FF validated failed.\n";
#			$ff_states_evaluated = -1;
#		}

		my $lifted_output = substr(`ulimit -v 2048000 && ./mypop $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | egrep "visited|length"`, 0, -1);
		my @lifted_lines = split(/\n/, $lifted_output);
#		my $plan_valid = `VALfiles/validate $example_path/domain.pddl $example_path/pfile$count.pddl solution-$domain_name-pfile$count | grep "Plan valid"`;
#		if (length($plan_valid) lt 1)
#		{
#			print "Lifted validated failed.\n";
#			$states_evaluated = -1;
#		}

		my @lifted_states = split(/ /, $lifted_lines[0]);
		my @lifted_plan_length = split(/ /, $lifted_lines[1]);
#		my @ff_states = split(/ /, $ff_lines[0]);
#		my @ff_plan_length = split(/ /, $ff_lines[1]);
#		print "$count - Lifted: @lifted_states[2] - Plan length: @lifted_plan_length[2]; FF: @ff_states[2] - Plan length: @ff_plan_length[2]\n";
		print "$count - Lifted: @lifted_states[2] - Plan length: @lifted_plan_length[2]\n";
	}
}
