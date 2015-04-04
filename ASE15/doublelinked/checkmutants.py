import subprocess
import glob
import sys

killed = []
live = []
other = []
total = 0

mutated = sys.argv[1]
unwind = sys.argv[2]

present = ["harness","dllinsert"]

present.remove(mutated)

pstring = ""

for p in present:
    pstring += p + ".c "

print "SANITY CHECK..."

results = "original_" + mutated + ".c.result"
resultF = open(results,'w')
subprocess.call(["cbmc " + pstring  + mutated + ".c" + 
                 " --bounds-check --pointer-check --slice-formula --unwind " + unwind],
                shell=True, stdout = resultF, stderr = resultF)
resultF.close()
normal = False
for l in open(results):
    if "VERIFICATION SUCCESSFUL" in l:
        normal = True
        break
if not normal:
    print "ORIGINAL CODE DOES NOT VERIFY!"
    sys.exit(1)
else:
    print "SANITY CHECK OK (ORIGINAL CODE VERIFIES SUCCESSFULLY)"

for f in glob.glob("mutant*" + mutated + ".c"):
    total += 1
    print "Checking mutant",f + ": ",
    results = f + ".result"
    if True:
        resultF = open(results,'w')
        subprocess.call(["cbmc " + pstring  + f + 
                         " --bounds-check --pointer-check --slice-formula --unwind " + unwind],
                        shell=True, stdout = resultF, stderr = resultF)
        resultF.close()
    normal = False
    for l in open(results):
        if "VERIFICATION SUCCESSFUL" in l:
            live.append(f)
            print "VERIFICATION SUCCESSFUL"
            normal = True
            break
        if "VERIFICATION FAILED" in l:
            killed.append(f)
            print "KILLED"
            normal = True
            break
    if not normal:
        print "OTHER RESULT"
        other.append(f)

print total, "TOTAL MUTANTS,", len(killed), "KILLED,", len(other), "FAILED TO COMPILE (" + str((len(killed) * 1.0)/(total*1.0) * (100.0)) + "% kill rate)"
print "SURVIVING MUTANTS:"
for f in live:
    print f
    subprocess.call(["grep MUTANT " + f], shell=True)


