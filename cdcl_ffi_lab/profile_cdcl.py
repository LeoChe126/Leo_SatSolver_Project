#!/usr/bin/env python3
"""Profile solve() in your existing CDCL/cdcl.py without the batch runner.

Usage:
    python3 profile_cdcl.py /home/yche/SatSolver/CDCL/cdcl.py /path/to/small.cnf
    python3 profile_cdcl.py /home/yche/SatSolver/CDCL/cdcl.py /path/to/small.cnf --output profile.pstats
"""
import argparse
import cProfile
import importlib.util
import pstats
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("solver", help="path to current CDCL/cdcl.py")
    ap.add_argument("cnf", help="one modest-size CNF to profile")
    ap.add_argument("--output", default="cdcl_profile.pstats")
    args = ap.parse_args()

    path = Path(args.solver).resolve()
    spec = importlib.util.spec_from_file_location("cdcl_to_profile", str(path))
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    nv, clauses = module.parseFile(Path(args.cnf).read_text())
    solver = module.CDCLSolver(clauses, nv)
    profiler = cProfile.Profile()
    print(f"Profiling: {path.name} | {Path(args.cnf).name} | vars={nv}, clauses={len(clauses)}")
    result = profiler.runcall(solver.solve)
    profiler.dump_stats(args.output)
    print(f"Verdict: {'SAT' if result is True else 'UNSAT' if result is False else result}")
    print(f"decisions={solver.num_decisions:,}, conflicts={solver.num_conflicts:,}, propagations={solver.num_propagations:,}")
    print("\nTop 20 by total CPU time in function (tottime):")
    pstats.Stats(profiler).strip_dirs().sort_stats("tottime").print_stats(20)
    print("\nTop 20 by total cumulative time (cumtime, includes callees):")
    pstats.Stats(profiler).strip_dirs().sort_stats("cumulative").print_stats(20)
    print(f"Saved profiling stats: {args.output}")
    print("Note: profiling adds overhead. Use unprofiled runs for runtime comparisons.")

if __name__ == "__main__":
    main()
