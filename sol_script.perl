#!/usr/bin/perl -w

use strict;
use warnings;

my $domain_name = shift(@ARGV);
my $from_problem_count = shift(@ARGV);
my $problem_count = shift(@ARGV);

print "$domain_name . $from_problem_count . $problem_count";

#for (my $prob = 0; $prob < scalar(@domain_arr); $prob++)
#{
    my $example_path = "../../domains/$domain_name";
    my $output_path = "results";
    
    print $domain_name."\n";
    
    system ("mkdir -p $output_path");
    
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
	print $count . "\n";

	#do planning
#	open RESULT, "<$output_path/${domain_name}_pfile$count\_marvin" or die "Unable to create raw output file";
	`./mypop $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1`;
	`cp lollipop_rpg_results $output_path/${domain_name}_pfile$count`;

	# Compare this output with marvin's.
	print "Search for: ../../marvin-bram/$output_path/${domain_name}_pfile$count\_marvin\n";
	open MARVIN_OUTPUT, "<../../marvin-bram/$output_path/${domain_name}_pfile$count\_marvin" or die "Unable to find marvin's output file";
	open LOLLIPOP_OUTPUT, "<$output_path/${domain_name}_pfile$count" or die "Unable to find LolliPOP's output file";
	
	my @marvin = <MARVIN_OUTPUT>;
	my @lollipop = <LOLLIPOP_OUTPUT>;

	close MARVIN_OUTPUT;
	close LOLLIPOP_OUTPUT;

	foreach my $m (@marvin)
	{
		my $found = 0;
		foreach my $l (@lollipop)
		{
			if ($m eq $l)
			{
				$found = 1;
				print "WHUT!?\n";
				exit;
			}
		}

		if ($found == 0)
		{
			print "Could not find the fact $m in the LolliPOP output!\n";
		}
		else
		{

			print "FOUND the fact $m in the LolliPOP output!\n";
		}
	}


	foreach my $l (@lollipop)
	{
		my $found = 0;
		foreach my $m (@marvin)
		{
			if ($m eq $l)
			{
				$found = 1;
				print "AHA";
			}
		}

		if ($found == 0)
		{
			print "Could not find the fact $l in the Marvin output!\n";
		}
		else
		{

			print "FOUND the fact $l in the Marvin output!\n";
		}
	}
    }
#}

