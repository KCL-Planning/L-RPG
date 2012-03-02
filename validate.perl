#!/usr/bin/perl -w

use strict;
use warnings;

#my @domain_names = ("driverlog", "satellite", "zeno", "gripper", "rovers", "storage", "depots", "blocksworld");
my @domain_names = ("storage");
my @from_domain_sizes = (1, 1, 1, 1, 1, 1, 1, 1);
my @to_domain_sizes = (20, 20, 20, 20, 20, 20, 20, 20);

for ( 0..$#domain_names )
{
    my $domain_name = $domain_names[$_];
    my $from_problem_count = $from_domain_sizes[$_];
    my $to_problem_count = $to_domain_sizes[$_];

    print "$domain_name . $from_problem_count . $to_problem_count";
    my $example_path = "/home/bram/projects/domains/$domain_name";

    for (my $i = $from_problem_count; $i <= $to_problem_count; $i++)
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
	my $stuff = `./mypop -val $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1`;
	if ($? != 0)
	{
		print "Failed validation on $domain_name problem number $count!\n";
	} else {
		print "$domain_name $count is valid!\n";
	}
    }
}

