import subprocess
import scipy
import scipy.stats
import shutil
import glob
import os
import sys

dnull = open(os.devnull,'w')

module = "avl.py"
mutants = "output/*_mutant_*.py"
tstl_run = "tstl_rt --noCover --full"

TIMES = [10]
INCREMENT = 10

depth = 10
killed = []
stable = False

backup = module+".backup"

allMutants = glob.glob(mutants)

shutil.copy(module,backup)

lastKills = -1

neverKilled = set(allMutants)

while not stable:
    print "="*50
    print "DEPTH =",depth
    sys.stdout.flush()
    kills = 0
    for m in allMutants:
        # Prepare the mutant
        # print m,
        sys.stdout.flush()
        shutil.copy(m,module)
        try: os.remove(module.replace(".py",",pyc"))
        except: pass
        killed = False
        for TIME in TIMES:
            TIMEOUT = TIME * 2
            subprocess.call(["rm -rf *.test"],shell=True)
            subprocess.call(["ulimit -t" + str(TIMEOUT) + "; " + tstl_run + " --depth " + str(depth) + " --timeout " + str(TIME)],shell=True,stdout=dnull,stderr=dnull)
            if glob.glob("*.test") != []:
                killed = True
                break
        if killed:
            neverKilled.remove(m)
            kills += 1
            sys.stdout.write("X")
        else:
            sys.stdout.write("-")
        sys.stdout.flush()
        # Restore original code
        shutil.copy(backup,module)
    print
    print kills,"KILLS"
    sys.stdout.flush()
    if ((kills == lastKills) or (kills < (lastKills - 10))) and (kills > 0):
        stable = True
    else:
        depth += INCREMENT

print "REACHED STABILITY AT",depth,"WITH",kills,"KILLS"
print "NEVER KILLED:"
for m in neverKilled:
    print m
    
