import os
import csv
import numpy as np
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
        mse_list += [float(get_max_mse(particles)) / 1.0]
    return (np.quantile(mse_list, 0.1), np.quantile(mse_list, 0.5), np.quantile(mse_list, 0.9))

ret = ""
for i in range(1,51):
    low, mid, high = run(i)
    ret += str(i) + ", "+ str(mid) + ", " + str(low) + ", " + str(high) + "\n"
    out = open("data/summary", "w")
    out.write(ret)
    out.close()
    

