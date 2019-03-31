import os
import csv
import statistics
name = "kalman_particles"

def get_max_mse(num):
    f = open("data/" + str(num), "r")
    r = csv.reader(f)
    ret = None
    for row in r:
        ret = row

    return ret[0]



def run(particles):
    src = open(name + ".zls.pre", "r")
    src_str = src.read()
    out = open(name + ".zls","w")
    out.write("let parts = " + str(particles) + "\n" + src_str)
    src.close()
    out.close()

    os.system("make opt")

    mse_list = []
    for i in range(0,100):
        os.system("cat ../data | ./" + name + ".opt > data/" + str(particles))
        mse_list += [float(get_max_mse(particles))]
    return (statistics.mean(mse_list), statistics.stdev(mse_list))

ret = ""
for i in range(1,51):
    mean, std = run(i)
    ret += str(i) + ", "+ str(mean) + ", " + str(std) + "\n"
    out = open("data/summary", "w")
    out.write(ret)
    out.close()
    

