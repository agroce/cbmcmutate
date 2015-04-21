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
checkStrength = False
coverMode = False

print "USAGE: evalmuants.py <prefix> <timeout> [--ignoreKilled <prefix>] [--ignoreSurvived <prefix>] [--cbmc <PATH>] --options <options> --files <files> --mutate <mutant-files> [--harness] [--use-existing] [--check-strength] [--cover]"

if "--cover" in sys.argv:
    sys.argv.remove("--cover")
    coverMode = True

if "--harness" in sys.argv:
    sys.argv.remove("--harness")
    harnessMode = True

if "--check-strength" in sys.argv:
    sys.argv.remove("--check-strength")
    checkStrength = True    

if "--use-existing" in sys.argv:
    sys.argv.remove("--use-existing")
    useExisting = True

ignoreKilled = None
ignoreSurvived = None

prefix = sys.argv[1]
print "PREFIX =", prefix
timeout = sys.argv[2]
print "TIMEOUT =", timeout
pos = 3
cbmc = "cbmc"
nextCBMC=False
for o in sys.argv[pos:]:
    print nextCBMC,o
    pos += 1
    if nextCBMC:
        cbmc = o
        nextCBMC = False
    if o == "--options":
        break
    if o == "--cbmc":
        nextCBMC = True
if "--ignoreKilled" in sys.argv:
    print sys.argv
    ikpos = sys.argv.index("--ignoreKilled")
    ignoreKilled = sys.argv[ikpos+1]
    sys.argv = sys.argv[0:ikpos] + sys.argv[ikpos+2:]
    print sys.argv
if "--ignoreSurvived" in sys.argv:
    ispos = sys.argv.index("--ignoreSurvived")
    ignoreSurvived = sys.argv[ispos+1]
    sys.argv = sys.argv[0:ispos] + sys.argv[ispos+2:]    
options = ""
pos = sys.argv.index("--options")+1
for o in sys.argv[pos:]:
    pos += 1
    if o == "--files":
        break
    options += o + " "
print "OPTIONS =", options
files = []
for o in sys.argv[pos:]:
    pos += 1
    if o == "--mutate":
        break
    files.append(o)
print "FILES =", files
mutants = []
for o in sys.argv[pos:]:
    mutants.append(o)
print "MUTATED FILES =",mutants

mutp = "limit cputime " + timeout + " ; "
mutp += cbmc + " " + options

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
    
def mutateAll(mutants, files, totalSuccessTime, totalKilledTime, minSuccessTime, minKilledTime,
              maxSuccessTime, maxKilledTime, killed, live, timedout, other, total,
              harnessCall=None, mode="", indent=""):
    for mutant_base in mutants:
        print indent+"Mutating " + mutant_base
        keepsame = []
        for m in mutants:
            if m != mutant_base:
                keepsame.append(m)
        mprefix = "mutant*_"
        if coverMode:
            mprefix = "COVER_" + mprefix
        print "PREFIX:",mprefix
        for mutant in glob.glob(mprefix+mutant_base):
            total += 1
            print indent+"Checking mutant", mutant + ": ",
            printMutant(mutant)
            results = mutant + mode + ".result"
            ignoreIt = False
            if not (ignoreKilled == None):
                oldResult = ignoreKilled + "." + results
                for l in open(oldResult):
                    if "VERIFICATION FAILED" in l:
                        print "Skipping due to ignoreKilled"
                        cpcmd = "cp " + oldResult + " " + prefix + "." + results
                        subprocess.call([cpcmd], shell=True)
                        ignoreIt = True
                        break
            if not (ignoreSurvived == None):
                oldResult = ignoreSurvived + "." + results
                for l in open(oldResult):
                    if "VERIFICATION SUCCESSFUL" in l:
                        print "Skipping due to ignoreSurvived"
                        cpcmd = "cp " + oldResult + " " + prefix + "." + results
                        subprocess.call([cpcmd], shell=True)
                        ignoreIt = True
                        break
            if ignoreIt:
                continue                    
            (result, time) = checkMutant(mutant, keepsame+files, results)
            if result == True:
                print indent+"VERIFICATION SUCCESSFUL", time
                totalSuccessTime += time
                if (time > maxSuccessTime):
                    maxSuccessTime = time
                if (time < minSuccessTime):
                    minSuccessTime = time                
                if harnessMode and not harnessCall:
                    print "Mutated harness survived, checking kill rate for", mutant
                    print "-------------------------------------------------"
                    rate = mutateAll(files, [mutant], 0.0, 0.0, 100000000.0, 100000000.0, 0.0, 0.0, [], [], [], [], 0,
                                    harnessCall=True, mode="."+mutant, indent="   ")
                    print "Done checking kill rate for", mutant
                    if rate == harnessRate:
                        print "Mutated harness preserves kill rate."
                        live.append(mutant)
                    elif rate > harnessRate:
                        print "MUTATED HARNESS IMPROVES KILL RATE."
                        better.append((mutant, rate))
                    else:
                        print "Mutated harness has worse kill rate than base harness. (KILLED)"
                        killed.append(mutant)
                    print "-------------------------------------------------"
                else:
                    live.append(mutant)
                    totalSuccessTime += time
                    if (time > maxSuccessTime):
                        maxSuccessTime = time
                    if (time < minSuccessTime):
                        minSuccessTime = time
            if result == False:
                killed.append(mutant)
                totalKilledTime += time
                if (time > maxKilledTime):
                    maxKilledTime = time
                if (time < minKilledTime):
                    minKilledTime = time
                print indent+"KILLED", time
            if result == "TIMEOUT":
                timedout.append(mutant)
                print indent+"TIMEOUT"
            if result == None:
                print indent+"OTHER RESULT"
                other.append(mutant)
            sys.stdout.flush()
            sys.stderr.flush()

    print indent+str(total), "TOTAL MUTANTS,", len(killed), "KILLED,", len(other), "FAILED TO COMPILE", len(timedout), "TIMED OUT, (" + str((len(killed) * 1.0)/(total*1.0) * (100.0)) + "% kill rate)"
    if len(killed) > 0:
        print indent+"AVERAGE KILL TIME", (totalKilledTime/len(killed))
    if len(live) > 0:
        print indent+"AVERAGE VERIFY TIME", (totalSuccessTime/len(live))
    print indent+"MIN/MAX KILL TIME = ",minKilledTime,"/",maxKilledTime
    print indent+"MIN/MAX SUCCESS TIME = ",minSuccessTime,"/",maxSuccessTime
    if not harnessCall:
        print "SURVIVING MUTANTS:",len(live)
        if harnessMode:
            print "(SAME KILL RATE)"
        for f in live:
            print f
            printMutant(f)
        if harnessMode:
            print "(** BETTER KILL RATE **)"            
            for (f, rate) in better:
                print f
                printMutant(f)
                print "RATE: ", rate

                   
    return ((len(killed)*1.0)/(total*1.0))*100.0

print "SANITY CHECK..."
(checkOriginal, originalTime) = checkMutant("", mutants + files, "original.result")
if not checkStrength:
    assert ((checkOriginal == True) or (checkOriginal == "TIMEOUT"))
    print "Original SUCCESSFULLY VERIFIED in", originalTime
else:
    assert ((checkOriginal == False) or (checkOriginal == "TIMEOUT"))
    print "Original SUCCESSFULLY KILLED in",originalTime
sys.stdout.flush()
sys.stderr.flush()

if harnessMode:
    print "Computing base harness kill rate"
    print "-------------------------------------------------"
    harnessRate = mutateAll(files, [mutants[0]], originalTime, 0.0, originalTime, 100000000.0, originalTime, 0.0, [], [], [], [], 0,
                            harnessCall = True, mode="."+mutants[0], indent="   ")
    print "-------------------------------------------------"
    print "Done computing base kill rate"
    better = []

mutateAll(mutants, files, originalTime, 0.0, originalTime, 100000000.0, originalTime, 0.0, [], [], [], [], 0)




