import subprocess
import glob
import sys

killed = []
live = []
timedout = []
other = []
total = 0

prefix = sys.argv[1]
print "PREFIX =", prefix
timeout = sys.argv[2]
print "TIMEOUT =", timeout
options = ""
for o in sys.argv[3:]:
    options += o
print "OPTIONS =", options

mutp = "limit cputime " + timeout + " ; "
mutp += "~/cbmc/cbmc -I . " + options + " "

print mutp

def printMutant(mutant):
    n = 0
    for l in open(mutant):
        n += 1
        if "MUTANT" in l:
            print n,":",l,

def checkMutant(mutant, results):
    results = prefix + "." + results
    thisFake = open("mfake.c",'w')
    for l in open("fake.c"):
        if "tiny.c" not in l:
            thisFake.write(l)
        else:
            thisFake.write(l.replace("tiny.c",mutant))
    thisFake.close()        
    resultF = open(results,'w')
    subprocess.call([mutp + "mfake.c"],
                    shell=True, stdout = resultF, stderr = resultF)
    resultF.close()
    normal = False
    for l in open(results):
        if "VERIFICATION SUCCESSFUL" in l:
            return True
        if "VERIFICATION FAILED" in l:
            return False
        if "Cputime limit exceeded" in l:
            return "TIMEOUT"
    if not normal:
        return None

print "SANITY CHECK..."
checkOriginal = checkMutant("tiny.c", "original.result")
assert ((checkOriginal == True) or (checkOriginal == "TIMEOUT"))
print "Original SUCCESSFULLY VERIFIED"

for mutant in glob.glob("mutant*tiny.c"):
    total += 1
    print "Checking mutant", mutant + ": ",
    printMutant(mutant)
    results = mutant + ".result"
    result = checkMutant(mutant, results)
    if result == True:
        live.append(mutant)
        print "VERIFICATION SUCCESSFUL"
    if result == False:
        killed.append(mutant)
        print "KILLED"
    if result == "TIMEOUT":
        timedout.append(mutant)
        print "TIMEOUT"
    if result == None:
        print "OTHER RESULT"
        other.append(mutant)
    sys.stdout.flush()
    sys.stderr.flush()

print total, "TOTAL MUTANTS,", len(killed), "KILLED,", len(other), "FAILED TO COMPILE", len(timedout), "TIMED OUT, (" + str((len(killed) * 1.0)/(total*1.0) * (100.0)) + "% kill rate)"
print "SURVIVING MUTANTS:"
for f in live:
    print f
    printMutant(f) 


