import sys
import glob

mutant_base = sys.argv[1]

for infile in glob.glob("mutant*_" + mutant_base):

    outfile = "BRANCHCOV_" + infile

    outf = open(outfile,'w')

    newCode = []
    
    newCode.append ("int mutant_covered = 0;\n\n")
    newCode.append ("int total_covered = 0;\n\n")

    cnum = 0

    lprev = ["foo"]

    branchers = ["if","else","for","while"]
    
    for l in open(infile):
        if "/*" in l:
            inComment = True
        if not inComment:
            if "MUTANT" in l:
                sp = "";
                for c in l:
                    if c == " ":
                        sp += " "
                    else:
                        break
                newCode.append(sp + "mutant_covered = 1;\n")
            inCode = ((l[0] == " " or l[0] == "\t") and not (l.split()[0] == "else"))
            if inCode and (lprev[0] in branchers):
                sp = "";
                for c in l:
                    if c == " ":
                        sp += " "
                    elif c == "\t":
                        sp += "\t"
                    else:
                        break            
                newCode.append(sp + "if (!__covered" + str(cnum) + ") {__covered" + str(cnum) + " = 1; total_covered += 1;}\n")
                cnum += 1
        if "*/" in l:
            inComment = False
        lprev = l.split()
        if lprev == []:
            lprev = ["foo"]
        newCode.append(l)

    for i in xrange(0,cnum):
        outf.write("int __covered"+str(i)+";\n")
    for l in newCode:
        outf.write(l)
    outf.close()
