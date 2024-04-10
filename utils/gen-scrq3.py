# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions"
# by Anonymous Authors.
# 
# Artifact by Anonymous Author, 2024. 
#
# Script for generating RQ3's scatter plot.
# Usage: python3 ./gen-scrq3.py DAFNY-RESULTS BOOGIE-RESULTS

import sys

if len(sys.argv) != 3:
    print(f"Usage: python {sys.argv[0]} DAFNY-RESULTS BOOGIE-RESULTS", file=sys.stderr)
    sys.exit(1)

dafny = sys.argv[1]
boogie = sys.argv[2]

# These are ghost-only methods unreported in our benchmarks.
exclude = {'bst-scaffolding::fix-depth', 'scheduler-queue::bst-fix-depth'}

def generate_times(data):
    # Collect benchmark names and times together.
    lines = [dd for dd in data if dd.strip() != '' and not dd.strip().endswith(':') and '==' not in dd and "not run" not in dd]
    time_raw = lambda x: x.split('(')[0].strip()
    hours = lambda x: float(time_raw(x).split('h')[0].strip())
    minutes = lambda x: float(time_raw(x).split('h')[1].split('m')[0].strip())
    seconds = lambda x: float(time_raw(x).split('m')[1].split('s')[0].strip())
    total = lambda x: hours(x)*3600 + minutes(x)*60 + seconds(x)

    benchmark = lambda x: x.split('(')[1].split(')')[0].strip()

    time_data = {benchmark(ll): total(ll) for ll in lines}

    # Combine impact set verif. time with method verif. time. 
    combine = lambda x, y: x + "::" + y
    datastructure = lambda x: x.split('::')[0]
    method = lambda x: x.split('::')[1]

    benchnames = list(time_data.keys())

    for benchname in benchnames:
        if method(benchname) != "impact-sets":
            time_data[benchname] += time_data[
                combine(datastructure(benchname), "impact-sets")
            ]

    # Exclude impact sets and methods in `exclude`.
    for benchname in benchnames:
        if method(benchname) == "impact-sets"\
            or benchname in exclude:
            del time_data[benchname]

    return time_data


with open(dafny, 'r') as f:
    dafny_data = f.read().split('\n')

dafny_dict = generate_times(dafny_data)

with open(boogie, 'r') as f:
    boogie_data = f.read().split('\n')

boogie_dict = generate_times(boogie_data)

# line up the data from smallest to largest boogie times
paired_times = sorted([(dafny_dict[kk], boogie_dict[kk]) for kk in dafny_dict.keys()], key=lambda z: z[1])
dafny_time_arr = [tt[0] for tt in paired_times]
boogie_time_arr = [tt[1] for tt in paired_times]

# Plotting code starts here
import matplotlib.pyplot as plt
import numpy as np

plt.figure(figsize=(6, 5))

x = dafny_time_arr
y= boogie_time_arr

plt.xlabel("Dafny Verification Time (s)", fontsize=12)
plt.xscale('log')
plt.ylabel("Boogie Verification Time (s)", fontsize=12)
plt.xticks(fontsize=15)
plt.yticks(fontsize=15)

axes = plt.gca()

plt.scatter(x,y, c='xkcd:royal blue', s=15)
#plt.axline([0,0], slope=1)
y_limit = axes.get_ylim()[1]
xx = np.linspace(0,y_limit,100)
plt.plot(xx,xx,c='darkgray')
#plt.plot(100*xx,xx)
plt.text(xx[-4],xx[-4], ' y=x', fontsize=15)

plt.savefig('scatter.png')
