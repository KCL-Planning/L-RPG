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

my $now = strftime "%Y_%m_%d-%H", localtime;

my $output_path = "heuristic-values-at-$now";
    
system ("mkdir -p $output_path");
system ("mkdir -p latest_heuristics_results");
system ("mkdir -p latest_heuristics_results/grounded");
system ("mkdir -p latest_heuristics_results/lifted");

#foreach my $domain_name (@domain_names)
{
	#my $example_path = "/home/bram/projects/domains/$domain_name";
	my $example_path = "../../planning/domains/$domain_name";
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
#		my $ff_states_evaluated = substr(`ulimit -t 600 && ./mypop -ff $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | grep "Best" | awk '{print \$4}'`, 0, -1);
	#	my $ff_plan_length = substr(`ulimit -t 600 && ./mypop -ff $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | grep "Plan length" | awk '{print \$3}'`, 0, -1);
#		my $ff_plan_valid = `VALfiles/validate $example_path/domain.pddl $example_path/pfile$count.pddl solution-$domain_name-pfile$count | grep "Plan valid"`;
#		if (length($ff_plan_valid) lt 1)
#		{
#			print "FF validated failed.\n";
#			$ff_states_evaluated = -1;
#		}

		my $grounded_output = substr(`ulimit -t 1800 && ./mypop -g $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | egrep "visited|Length" | awk '{print \$3;}'`, 0, -1);
		my @grounded_plan_data = split(/\n/, $grounded_output);
		print "Grounded: $count - States evaluated: $grounded_plan_data[0] - Plan length: $grounded_plan_data[1]\n";
		my $lifted_output = substr(`ulimit -t 1800 && ./mypop $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | egrep "visited|Length" | awk '{print \$3;}'`, 0, -1);
		my @lifted_plan_data = split(/\n/, $lifted_output);
		print "Lifted: $count - States evaluated: $lifted_plan_data[0] - Plan length: $lifted_plan_data[1]\n";
#		my $lifted_plan_length = substr(`ulimit -t 600 && ./mypop $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | grep "Plan length" | awk '{print \$3}'`, 0, -1);
#		`echo "$count $states_evaluated" >> $output_path/${domain_name}.data`;
#		my $plan_valid = `VALfiles/validate $example_path/domain.pddl $example_path/pfile$count.pddl solution-$domain_name-pfile$count | grep "Plan valid"`;
#		if (length($plan_valid) lt 1)
#		{
#			print "Lifted validated failed.\n";
#			$states_evaluated = -1;
#		}
		#print "$count - Lifted: $states_evaluated \n";
		`echo "$count $grounded_plan_data[0]" >> $output_path/states_grounded_${domain_name}.data`;
		`echo "$count $grounded_plan_data[1]" >> $output_path/quality_grounded_${domain_name}.data`;
		`echo "$count $lifted_plan_data[0]" >> $output_path/states_lifted_${domain_name}.data`;
		`echo "$count $lifted_plan_data[1]" >> $output_path/quality_lifted_${domain_name}.data`;
#		print "$count - Lifted: $states_evaluated v.s. FF: $ff_states_evaluated\n";
#		print "$count - Lifted: $lifted_plan_length v.s. FF: $ff_plan_length\n";
		`cp $output_path/states_grounded_${domain_name}.data latest_heuristics_results/grounded/${domain_name}.data`;
		`cp $output_path/quality_grounded_${domain_name}.data latest_heuristics_results/grounded/${domain_name}_length.data`;
		`cp $output_path/states_lifted_${domain_name}.data latest_heuristics_results/lifted/${domain_name}.data`;
		`cp $output_path/quality_lifted_${domain_name}.data latest_heuristics_results/lifted/${domain_name}_length.data`;
	}
}
