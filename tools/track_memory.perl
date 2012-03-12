#!/usr/bin/perl -w

use strict;
use warnings;

my $program_name = shift(@ARGV);
print "Track memory for $program_name\n";
my $pid = `ps aux | grep $program_name | egrep -v "grep|perl" | awk \'{print \$2}'`;

my @pids = split('\n', $pid);
if (scalar(@pids) eq 0)
{
	exit;
}
print "Found PID: $pid\n";

open (MEM_FILE, '>memory_results');

while (1)
{
	foreach my $p (@pids)
	{
		my $memory = substr `pmap $p | grep total | awk \'{print \$2}\'`, 0, -2;
		my $unit = "Kb";
		if ($memory gt 1024 * 1024)
		{
			$memory /= 1024 * 1024;
			$unit = "Gb";
		}
		elsif ($memory gt 2048)
		{
			$memory /= 1024;
			$unit = "Mb";
		}
		print MEM_FILE $memory;
		print "Memory: for $p is $memory $unit\n";
	}
	# Check if the PIDS are still there.
	my $test_pid = `ps aux | grep $program_name | egrep -v "grep|perl" | awk \'{print \$2}'`;
	my @test_pids = split('\n', $test_pid);

	if (scalar(@test_pids) eq 0)
	{
		last;
	}

	sleep(1);
}

close MEM_FILE;
