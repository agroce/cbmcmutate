import sys

def compare(fname1,fname2):
	f = open(fname1, 'r')
	f2 = open(fname2, 'r')
	f.readline() # usage
	f2.readline() # usage
	f.readline() # prefix
	f2.readline() # prefix
	f.readline() # timeout
	f2.readline() # timeout
	f.readline() # options
	f2.readline() # options
	f.readline() # files
	f2.readline() # files
	f.readline() # mutated files
	f2.readline() # mutated files
	f.readline() # limit
	f2.readline() # limit
	f.readline() # samity check
	f2.readline() # samity check
	f.readline() # original
	f2.readline() # original
	f.readline() # mutating
	f2.readline() # mutating
	line = f.readline()
	line2 = f2.readline()
	while line.startswith("Checking"):
		checkline = line
		if line != line2:
			print line
			print line2
			line = f.readline()
			line2 = f2.readline()
			print fname1, line.rstrip()
			print fname2, line2.rstrip()
			print
		else:
			line = f.readline()
			line2 = f2.readline()

			if line.split()[0] != line2.split()[0]:
				print checkline.rstrip()
				print fname1, line.rstrip()
				print fname2, line2.rstrip()
				print 

		line = f.readline()
		line2 = f2.readline()
	f.close()

if len(sys.argv) == 3:
	compare(sys.argv[1], sys.argv[2])
else:
	print "Usage example: python compareharness.py checkgoodharness3.out checkbadharness3.out "