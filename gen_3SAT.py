import random, sys
n = int(sys.argv[1]); m = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv)>3 else 0
random.seed(seed)
print(f"p cnf {n} {m}")
for _ in range(m):
    vs = random.sample(range(1, n+1), 3)
    print(" ".join(str(v if random.random()<.5 else -v) for v in vs) + " 0")
