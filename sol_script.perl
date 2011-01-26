#!/usr/bin/perl -w
#usr/bin/bash

use strict;
use warnings;

my $domain_name = shift(@ARGV);
my $from_problem_count = shift(@ARGV);
my $problem_count = shift(@ARGV);
my $planner = shift(@ARGV);

#for (my $prob = 0; $prob < scalar(@domain_arr); $prob++)
#{
    my $example_path = "/home/s1/apasshared/domains/$domain_name";
    my $output_path = "results";
    my $val_path = "/home/s5/pattison/WWW/validate";
    my $trunc_results = "./".$domain_name."_results";
    my $raw_output = "_raw";
    my $sol_output = "_sol";
    
    open OUT, ">$trunc_results" or die "Unable to create truncated output file";
    
    print OUT $domain_name."\n";
    
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
	print OUT $count;

	#do planning
	if ($j % 10 == 0)
	{
#		printf "%16s %24s %24s %24s %24s %24s %24s\n", "Results", "Plans generated", "Plans visited", "Dead ends", "Time taken (ms.)", "Plan length", "Valid?";
		printf "%16s %24s %24s %24s %24s %24s %24s\n", "Results", "Time taken (ms.)", "Plan length", "Plans generated", "Plans visited", "Dead ends", "Valid?";
	}
	printf "%16s", "[$count] Planning... ";
	open RAW_OUT, ">$output_path/${domain_name}_${planner}_pfile$count\_raw" or die "Unable to create raw output file";
	open (PLAN, "ulimit -t 600 && nice -19 ./$planner 3 $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 |");
	my @steps = ();
	while (<PLAN>)
	{
		if ($_ =~ m/Step \d+.*(\(.*\))/)
		{
			push (@steps, $1);
		}
		print RAW_OUT $_;

	}	
	close PLAN;
	close RAW_OUT;

	my $str = (`cat $output_path/${domain_name}_${planner}_pfile$count\_raw | egrep "Plans|Time|Dead|Number" | sed ':a;N;\$!ba;s/\\n/ - /g'`);
	chop($str);

	my @numbers = ($str =~ m/([\d\.]+)/g);
	if (scalar(@numbers) == 5)
	{
		printf "%24s %24s %24s %24s %24s", $numbers[0], $numbers[1], $numbers[2], $numbers[3], $numbers[4];
	} else {
		printf "%24s %24s %24s %24s %24s", "-", "-", "-", "-", scalar(@steps);
	}

	# Print the solution in a solution file.
	open SOL_OUT, ">$output_path/${domain_name}_${planner}_pfile$count\_sol" or die "Unable to create solution output file";
#	foreach my $step (@steps)
	for (my $k = 1; $k < $#steps; $k++)
	{
#		print SOL_OUT "$step\n";
		print SOL_OUT "$steps[$k]\n";
	}
	close SOL_OUT;

	#validate
#	print "[$count] Validating... ";
	open RAW_VAL, ">$output_path/${domain_name}_${planner}_pfile$count\_val" or die "Unable to create raw output file";
	open (VAL, "$val_path -v $example_path/domain.pddl $example_path/pfile$count.pddl $output_path/${domain_name}_${planner}_pfile$count\_sol |");
	while (<VAL>)
	{
		print RAW_VAL $_;
		my $ptime = m/Failed plans/;
		if ($ptime)
		{
			printf "%24s", "INVALID :'(\n";
		}
		$ptime = m/Plan valid/;
		if ($ptime)
		{
			printf "%24s", "VALID :D\n";
		}
	}

	close VAL;
	close RAW_VAL;
    }
#}

close OUT;
