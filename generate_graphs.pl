@lines = `ls *.dot`;
foreach $line (@lines) {
	# Strip the extention.
	$stripped_name = substr($line, 0, rindex($line, "."));
	print "Processing: $stripped_name ...  ";
	$no_eol_line = substr($line, 0, -1);
	$no_eol_line =~ s/\(/\\\(/g;
	$no_eol_line =~ s/\)/\\\)/g;
	$no_eol_line =~ s/\{/\\\{/g;
	$no_eol_line =~ s/\}/\\\}/g;

	print "-=- dot -Tsvg -o $stripped_name.svg \"$no_eol_line\" -=- ";
	# Dot this shit :).
#	`dot -Tpng -o $stripped_name.png $line`;
#	`dot -Tpdf -o $stripped_name.pdf $line`;
	`dot -Tsvg -o \"$stripped_name.svg\" \"$no_eol_line\"`;

	print "Done!\n";
}
