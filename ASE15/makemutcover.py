import sys

infile = sys.argv[1]
outfile = sys.argv[2]

outf = open(outfile,'w')

outf.write ("int mutant_covered = 0;\n\n")

for l in open(infile):
    if "MUTANT" in l:
        sp = " ";
        for c in l:
            if c == " ":
                sp += " "
            else:
                break
        outf.write(sp + "mutant_covered = 1;\n")
    outf.write(l)

outf.close()
