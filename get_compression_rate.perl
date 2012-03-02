#!/usr/bin/perl -w

use strict;
use warnings;

#my $domain_name = shift(@ARGV);
#my @domain_names = ("pipesnotankage", "freecell", "airport", "mystery");
my @domain_names = ("scalable_storage");
#my @domain_names = ("driverlog", "satellite", "zeno", "gripper", "rovers", "storage", "depots", "blocksworld");
#my @domain_names = ("big_driverlog", "big_depots", "big_satellite", "big_zeno");
my $from_problem_count = shift(@ARGV);
my $problem_count = shift(@ARGV);
    
system ("mkdir -p compression_rates");

foreach my $domain_name (@domain_names)
{
	my $example_path = "/home/bram/projects/domains/$domain_name";
	print "$domain_name . $from_problem_count . $problem_count";
	print $domain_name."\n";

	`rm compression_rates/${domain_name}.data`;
	    
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

#		my $stuff = `./mypop -val $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1`;
#		if ($? != 0)
#		{
#			print "Failed validation on $domain_name problem number $count!\n";
#			next;
#		}

		#do planning
		my $compression_rate = 100.0 - substr(`./mypop $example_path/domain.pddl $example_path/pfile$count.pddl 2>&1 | grep "Compression" | awk '{print \$3}'`, 0, -1);
		print "$count - $compression_rate\n";
		`echo "$compression_rate" >> compression_rates/${domain_name}.data`;
	}
}
