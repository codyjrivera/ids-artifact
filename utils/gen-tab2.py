# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions"
# by Anonymous Authors.
# 
# Artifact by Anonymous Author, 2024. 
#
# Script for generating numbers to be used in Table 2.
# Usage: python3 ./gen-tab2.py RESULTS

import sys

if len(sys.argv) != 2:
    print(f"Usage: python {sys.argv[0]} RESULTS", file=sys.stderr)
    sys.exit(1)

boogie = sys.argv[1]

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

with open(boogie, 'r') as f:
    boogie_data = f.read().split('\n')

boogie_dict = generate_times(boogie_data)

for name, time in boogie_dict.items():
    print("{:6.2f}s:    ({})".format(time, name))
