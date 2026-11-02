# Profiling and Python↔C++ FFI lab for CDCL

This lab **does not replace your solver**, and the native kernel is **not a complete CDCL solver**. Its purpose is to measure execution costs and learn how to call a C++ function from Python.

## Step 1: compile the shared library on asimov

```bash
cd /home/yche/SatSolver
mkdir -p perf_lab
# Copy ffi_kernels.cpp, ffi_bench.py, and profile_cdcl.py from this archive into perf_lab
cd perf_lab
g++ -std=c++17 -O3 -fPIC -shared ffi_kernels.cpp -o libffi_kernels.so
file libffi_kernels.so
```

- `-O3`: optimized native code
- `-fPIC -shared`: produces a shared library (`.so`)
- `extern "C"`: exports unmangled C function names that `ctypes` can resolve
- `ctypes.CDLL`: loads the C++ library into the running Python process
- `argtypes` and `restype`: tell Python how to convert data at the boundary

## Step 2: microbenchmarks (synthetic inputs)

```bash
python3 ffi_bench.py
```

Then use representative literal data from an actual CNF:

```bash
python3 ffi_bench.py --cnf "/path/to/actual.cnf" --n 1000 --repeats 2000
```

Compare: native batched kernel vs Python loop; repeated FFI calls vs one bulk call; `list.pop(0)` vs `deque.popleft()` vs list+head-index. All paths are checksum verified. **The native example evaluates literals; it does not implement SAT propagation or learn clauses.**

## Step 3: cProfile the actual Python solver

Choose a representative **small** CNF from QuICC batch-05 (not an entire folder):

```bash
first_file=$(find "QuICC-SAT-Datasets/DARPA QuICC Phase I Datasets 2025/batch-05" -type f -name '*.cnf' | sort | head -1)
python3 perf_lab/profile_cdcl.py CDCL/cdcl.py "$first_file" --output perf_lab/solve.pstats
```

Or simply from the project root:

```bash
python3 -m cProfile -o cdcl_run.pstats CDCL/cdcl.py benchmarks/quicc-test10 profile_results.csv
python3 - <<'PY'
import pstats
pstats.Stats('cdcl_run.pstats').strip_dirs().sort_stats('cumulative').print_stats(25)
PY
```

**Important**: if the batch runner forks worker processes, profile the worker or direct `solve()` using `profile_cdcl.py`. Parent-process profiling often shows mostly `multiprocessing` waiting rather than actual solver cost.

## Interpreting results

- `tottime` is time spent in a function excluding callees; `cumtime` includes callees.
- High `propagate` and `remove_watch` total time suggests watched-literal engine work.
- High `minimize_learned_clause` total time suggests recursive redundancy checks.
- High `choose_literal_vsids` total time suggests variable scoring/selection overhead.
- High `reduce_clause_database` total time suggests deletion bookkeeping.
- Results from this lab are **machine-specific**. Run all variants on the *same* server and CPU, with the *same* file and settings, repeating runs for median timings.
- Measure both runtime and algorithmic counters. If the counters change, the search path changed; that is not merely runtime overhead.
- A single FFI call per watch/literal is usually counterproductive. Use native code for whole kernels or persistent solver state.

## Sources

Python ctypes documentation: https://docs.python.org/3.13/library/ctypes.html
Python cProfile/pstats documentation: https://docs.python.org/3.13/library/profile.html
