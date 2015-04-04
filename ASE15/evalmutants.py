import subprocess
import glob
import sys
import os

killed = []
live = []
timedout = []
other = []
total = 0

harnessMode = False
useExisting = False

print "USAGE: evalmuants.py <prefix> <timeout> --options <options> --files <files> --mutate <mutant-files> [--harness] [--use-existing]"

if "--harness" in sys.argv:
    sys.argv.remove("--harness")
    harnessMode = True

if "--use-existing" in sys.argv:
    sys.argv.remove("--use-existing")
    useExisting = True

prefix = sys.argv[1]
print "PREFIX =", prefix
timeout = sys.argv[2]
print "TIMEOUT =", timeout
pos = 4
options = ""
for o in sys.argv[pos:]:
    pos += 1
    if o == "--files":
        break
    options += o + " "
print "OPTIONS =", options
files = ""
for o in sys.argv[pos:]:
    pos += 1
    if o == "--mutate":
        break
    files += o + " "
print "FILES =", files
mutants = []
for o in sys.argv[pos:]:
    mutants.append(o)
print "MUTATED FILES =",mutants

mutp = "limit cputime " + timeout + " ; "
mutp += "cbmc " + options + files

print mutp

def printMutant(mutant):
    n = 0
    for l in open(mutant):
        n += 1
        if "MUTANT" in l:
            print n,":",l,

def checkMutant(mutant, keepsame, results):
    fkeepsame = ""
    for k in keepsame:
        fkeepsame += k + " "
    results = prefix + "." + results
    if (not useExisting) or (not os.path.exists(results)):
        resultF = open(results,'w')
        subprocess.call([mutp + fkeepsame + mutant],
                        shell=True, stdout = resultF, stderr = resultF)
        resultF.close()
    normal = False
    for l in open(results):
        if "Runtime decision" in l:
            time = float((l.split()[-1])[:-1])
        if "VERIFICATION SUCCESSFUL" in l:
            return (True, time)
        if "VERIFICATION FAILED" in l:
            return (False, time)
        if "Cputime limit exceeded" in l:
            return ("TIMEOUT", None)
    if not normal:
        return (None, None)

totalSuccessTime = 0.0
maxSuccessTime = 0.0
minSuccesstime = 100000000.0
totalKilledTime = 0.0
maxKilledTime = 0.0
minKilledTime = 100000000.0

print "SANITY CHECK..."
(checkOriginal, originalTime) = checkMutant("", mutants, "original.result")
assert ((checkOriginal == True) or (checkOriginal == "TIMEOUT"))
totalSuccessTime += originalTime
maxSuccessTime = originalTime
minSuccessTime = originalTime
print "Original SUCCESSFULLY VERIFIED in", originalTime
sys.stdout.flush()
sys.stderr.flush()

for mutant_base in mutants:
    print "Mutating " + mutant_base
    keepsame = []
    for m in mutants:
        if m != mutant_base:
            keepsame.append(m)
    for mutant in glob.glob("mutant*"+mutant_base):
        total += 1
        print "Checking mutant", mutant + ": ",
        printMutant(mutant)
        results = mutant + ".result"
        (result, time) = checkMutant(mutant, keepsame, results)
        if result == True:
            live.append(mutant)
            totalSuccessTime += time
            if (time > maxSuccessTime):
                maxSuccessTime = time
            if (time < minSuccessTime):
                minSuccessTime = time
            print "VERIFICATION SUCCESSFUL", time
        if result == False:
            killed.append(mutant)
            totalKilledTime += time
            if (time > maxKilledTime):
                maxKilledTime = time
            if (time < minKilledTime):
                minKilledTime = time
            print "KILLED", time
        if result == "TIMEOUT":
            timedout.append(mutant)
            print "TIMEOUT"
        if result == None:
            print "OTHER RESULT"
            other.append(mutant)
        sys.stdout.flush()
        sys.stderr.flush()

print total, "TOTAL MUTANTS,", len(killed), "KILLED,", len(other), "FAILED TO COMPILE", len(timedout), "TIMED OUT, (" + str((len(killed) * 1.0)/(total*1.0) * (100.0)) + "% kill rate)"
if len(killed) > 0:
    print "AVERAGE KILL TIME", (totalKilledTime/len(killed))
if len(live) > 0:
    print "AVERAGE VERIFY TIME", (totalSuccessTime/len(live))
print "MIN/MAX KILL TIME = ",minKilledTime,"/",maxKilledTime
print "MIN/MAX SUCCESS TIME = ",minSuccessTime,"/",maxSuccessTime
print "SURVIVING MUTANTS:"
for f in live:
    print f
    printMutant(f) 


