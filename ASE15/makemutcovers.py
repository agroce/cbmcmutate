import sys
import glob

mutant_base = sys.argv[1]

for infile in glob.glob("mutant*_" + mutant_base):

    outfile = "COVER_" + infile

    outf = open(outfile,'w')

    outf.write ("int mutant_covered = 0;\n\n")

    for l in open(infile):
        if "MUTANT" in l:
            sp = "";
            for c in l:
                if c == " ":
                    sp += " "
                else:
                    break
            outf.write(sp + "mutant_covered = 1;\n")
        outf.write(l)

    outf.close()
