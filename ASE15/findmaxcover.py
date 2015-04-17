import sys
import subprocess
import glob

prefix = sys.argv[1]
harness = sys.argv[2]
mutant_base = sys.argv[3]
start = int(sys.argv[4])

options = ""
for o in sys.argv[5:]:
    options += o + " "

print prefix
print harness
print mutant_base
print start

mutStrength = {}

for m in glob.glob("FULLCOV_mutant*_" + mutant_base):
    print "Analyzing mutant",m
    sys.stdout.flush()
    sys.stderr.flush()
    t = start
    foundCover = False
    while ((t > 0) and (not foundCover)):
        print "Trying to find",t,"covering execution..."
        sys.stdout.flush()
        sys.stderr.flush()        
        cmd = "scbmc " + m + " " + harness + " " + options + "--find-success -DCOVTARGET=" + str(t)
        results = prefix + "." + m + ".bestcover"
        resultF = open (results, 'w')
        print cmd
        subprocess.call([cmd], shell=True, stdout = resultF, stderr = resultF)
        for l in open (results):
            if "VERIFICATION FAILED" in l:
                print "Successful!"
                sys.stdout.flush()
                sys.stderr.flush()
                foundCover = True
                break
        if not foundCover:
            t -= 1
    if t == 0:
        print "Can't cover mutant at all!"
        sys.stdout.flush()
        sys.stderr.flush()
    mutStrength[m] = t

mstr = mutStrength.items()
mstrSort = sorted(mstr, key = lambda x: x[1], reverse=True)

print "STRENGTHS:"

for (m, str) in mstrSort:
    print str,":",m,
    n = 0
    for l in open(m):
        n += 1
        if "MUTANT" in l:
            print n,":",l,
    print
