# chatgpt generated file to compare the performance of differnet modes, for report and analysis 

import csv
import sys

def load_csv(path):
    rows = {}
    with open(path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row["file"].split("/")[-1]
            rows[name] = row
    return rows

def time_value(row):
    if row is None:
        return "MISSING"
    if row["verdict"] == "TIMEOUT":
        return "TIMEOUT"
    return f"{float(row['time']):.3f}"

if len(sys.argv) != 4:
    print("Usage: python3 compare_modes.py baseline.csv random.csv walksat.csv")
    sys.exit(1)

baseline = load_csv(sys.argv[1])
random = load_csv(sys.argv[2])
walksat = load_csv(sys.argv[3])

files = sorted(set(baseline) | set(random) | set(walksat))

print("file,baseline,random,walksat,walksat_unsat")
for name in files:
    b = baseline.get(name)
    r = random.get(name)
    w = walksat.get(name)

    walksat_unsat = ""
    if w is not None:
        walksat_unsat = w.get("walksat_unsat_count", "")

    print(f"{name},{time_value(b)},{time_value(r)},{time_value(w)},{walksat_unsat}")