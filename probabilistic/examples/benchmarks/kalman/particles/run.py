import os
import csv
name = "kalman_particles"

def run(particles):
    src = open(name + ".zls.pre", "r")
    src_str = src.read()
    out = open(name + ".zls","w")
    out.write("let parts = " + str(particles) + "\n" + src_str)
    src.close()
    out.close()

    os.system("make opt")
    os.system("cat ../data | ./" + name + ".opt > data/" + str(particles))

for i in range(1,51):
    run(i)

def get_max_mse(num):
    f = open("data/" + str(num), "r")
    r = csv.reader(f)
    ret = None
    for row in r:
        ret = row

    return ret[0]

ret = ""
for i in range(1,51):
    ret += str(i) + ", "+ get_max_mse(i) + "\n"
    out = open("data/summary", "w")
    out.write(ret)
    out.close()
    

