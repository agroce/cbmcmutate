import subprocess

for l in open("coveredmutants"):
    ls = l.split()
    fname = ls[2]
    copycover = "covtiny." + fname + ".bestcover"
    copymutant = fname.replace("BRANCHCOV_","")
    cp1 = "cp " + fname + " for_paul/"
    cp2 = "cp " + copycover + " for_paul/"
    cp3 = "cp " + copymutant + " for_paul/"
    subprocess.call ([cp1], shell=True)
    subprocess.call ([cp2], shell=True)
    subprocess.call ([cp3], shell=True)

