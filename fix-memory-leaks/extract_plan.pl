# Find the solution number.


open FILE, "result" or die $!;
@lines = <FILE>;
close FILE;

open OUT, ">slimm_result_tmp" or die $!;

sub GetNextSolutionNr {
	my ($line_nr) = @_;
	print "GetNextSolutionNr: $line_nr\n";

	# Search for the given plan number.
	for ($i = $line_nr; $i > -1; $i--) {
		if ($lines[$i] =~ m/\*\*\* Current plan:/) {
			if ($lines[$i + 1] =~ m/Plan: \[(\d+)\]/) {
				return $1;
			}
		}
	}

	return 0;
}

sub ExtractPlan {
	my ($plan_number, $line_nr) = @_;

	@tmp = ();

	print "ExtractPlan: $plan_number $line_nr\n";
	# Search for the given plan number.
	for ($i = $line_nr; $i > -1; $i--) {
		$line = $lines[$i];
		if ($line =~ m/Plan: \[$plan_number\]/) {
			for (; $i < $#lines; $i++) {
				$line = $lines[$i];
				
				#print OUT "$line";
				push(@tmp, $line);
				if ($line =~ m/Orderings.*/) {

					# Print everything backwards.
					for ($j = $#tmp; $j > -1; $j--) {
						print OUT $tmp[$j];
					}

					return $i;
				}
			}
		}
	}

	return 0;
}

# Start reading the file and search for the line 'Sulution!'
for ($i = $#lines; $i > -1; $i--) {
	$line = $lines[$i];
	if ($line =~ m/Solution\! Plan: \[(\d+)\]/)
	{
		$solution_number = $1;
		while ((my $line_nr = &ExtractPlan($solution_number, $i)) != 0) {
			$solution_number = &GetNextSolutionNr($line_nr);
		}
		last;
	}
}

# Reverse the file.
close OUT;

open OUTM, "<slimm_result_tmp" or die $!;
@lines = reverse <OUTM>;
close OUTM;

open OUTR, ">slimm_result" or die $!;
foreach $line (@lines) {
	print OUTR $line;
}

close OUTR;

print "Done";

