#!/usr/bin/env python3
"""Small, reproducible ctypes FFI experiment for SAT-like operations.

Example:
    g++ -std=c++17 -O3 -fPIC -shared ffi_kernels.cpp -o libffi_kernels.so
    python3 ffi_bench.py --cnf ../../benchmarks/quicc-batch05-test10/example.cnf
    python3 ffi_bench.py  # uses deterministic synthetic literals
"""
import argparse
import ctypes as ct
import random
import statistics
import time
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent


def measure(name, fn, rounds=5):
    samples = []
    result = None
    for _ in range(rounds):
        t0 = time.perf_counter()
        result = fn()
        samples.append(time.perf_counter() - t0)
    secs = statistics.median(samples)
    print(f"{name:<33} {secs:>11.6f} s   checksum={result}")
    return secs, result


def cnf_literals(path, limit):
    literals = []
    declared_vars = 0
    with open(path, encoding="utf-8") as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p "):
                fields = line.split()
                if len(fields) < 4 or fields[1] != "cnf":
                    raise ValueError("Expected DIMACS CNF (p cnf ...)")
                declared_vars = int(fields[2])
                continue
            if line.startswith("%"):
                break
            for token in line.split():
                lit = int(token)
                if lit:
                    literals.append(lit)
                    if len(literals) >= limit:
                        return literals, max(declared_vars, max(map(abs, literals)))
    if not literals:
        raise ValueError("No literals found in CNF")
    return literals, max(declared_vars, max(map(abs, literals)))


def python_count_satisfied(lits, values, n, repeats):
    satisfied = 0
    for r in range(repeats):
        index = r % n
        for _ in range(n):
            lit = lits[index]
            var = lit if lit > 0 else -lit
            val = values[var]
            if (lit > 0 and val == 1) or (lit < 0 and val == 0):
                satisfied += 1
            index += 1
            if index == n:
                index = 0
    return satisfied


def bench_queue(n=10000):
    def pop_front():
        queue = list(range(n))
        s = 0
        while queue:
            s += queue.pop(0)
        return s

    def pop_deque():
        queue = deque(range(n))
        s = 0
        while queue:
            s += queue.popleft()
        return s

    def index_queue():
        queue = list(range(n))
        s = 0
        head = 0
        while head < len(queue):
            s += queue[head]
            head += 1
        return s

    print(f"\nQueue microbenchmark ({n:,} elements; illustrative only):")
    a, aout = measure("list.pop(0)", pop_front)
    b, bout = measure("deque.popleft()", pop_deque)
    c, cout = measure("list + head index", index_queue)
    assert aout == bout == cout
    print(f"  pop(0)/deque: {a/b:.1f}x; pop(0)/index: {a/c:.1f}x")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--cnf", help="Optional DIMACS CNF; take the first --n literals")
    p.add_argument("--n", type=int, default=1000, help="Number of literals")
    p.add_argument("--vars", type=int, default=250, help="Synthetic variable count")
    p.add_argument("--repeats", type=int, default=2000, help="Full scan repetitions")
    p.add_argument("--ffi-calls", type=int, default=150000, help="Small function call count")
    p.add_argument("--queue-size", type=int, default=10000)
    args = p.parse_args()

    lib_path = HERE / "libffi_kernels.so"
    if not lib_path.is_file():
        raise SystemExit(f"Build the shared library first: g++ -std=c++17 -O3 -fPIC -shared {HERE/'ffi_kernels.cpp'} -o {lib_path}")
    lib = ct.CDLL(str(lib_path))
    lib.ffi_add_one.argtypes = [ct.c_int64]
    lib.ffi_add_one.restype = ct.c_int64
    lib.ffi_add_many.argtypes = [ct.c_int32]
    lib.ffi_add_many.restype = ct.c_int64
    lib.ffi_count_satisfied.argtypes = [ct.POINTER(ct.c_int32), ct.POINTER(ct.c_int8), ct.c_int32, ct.c_int32]
    lib.ffi_count_satisfied.restype = ct.c_int64

    rng = random.Random(42)
    if args.cnf:
        lits, nvars = cnf_literals(args.cnf, args.n)
    else:
        nvars = args.vars
        lits = [(1 if rng.getrandbits(1) else -1) * rng.randint(1, nvars) for _ in range(args.n)]
    values = [0] + [rng.getrandbits(1) for _ in range(nvars)]
    n = len(lits)
    print(f"Input: {n} literals, {nvars} variables; repeats={args.repeats}")

    # Allocate C-compatible buffers once. Do not include conversion cost in a kernel-only measurement.
    literals_c = (ct.c_int32 * n)(*lits)
    values_c = (ct.c_int8 * (nvars + 1))(*values)

    print("\nSAT-like literal evaluation kernel (same checksum required):")
    py_secs, py_sum = measure("Pure Python list loop", lambda: python_count_satisfied(lits, values, n, args.repeats))
    c_secs, c_sum = measure("One native C++ batch via ctypes", lambda: lib.ffi_count_satisfied(literals_c, values_c, n, args.repeats))
    assert py_sum == c_sum, f"Mismatched work: Python {py_sum}, native {c_sum}"
    print(f"  Native kernel speedup: {py_secs / c_secs:.1f}x (not whole-solver speedup)")
    conversion, _ = measure("Python->ctypes buffers ONCE", lambda: ((ct.c_int32 * n)(*lits), (ct.c_int8 * (nvars + 1))(*values)))
    print(f"  Copying inputs into ctypes buffers costs ~{conversion * 1000:.2f} ms per conversion")

    k = args.ffi_calls
    def many_python_function_calls():
        def add_one(x):
            return x + 1
        out = 0
        for i in range(k):
            out += add_one(i)
        return out

    def many_foreign_calls():
        out = 0
        for i in range(k):
            out += lib.ffi_add_one(i)
        return out

    print(f"\nFFI call-boundary experiment ({k:,} tiny operations):")
    py_calls_t, py_calls_sum = measure("Python function call each time", many_python_function_calls)
    ffi_calls_t, ffi_calls_sum = measure("ctypes call each time", many_foreign_calls)
    one_call_t, one_call_sum = measure("ONE ctypes call for all", lambda: lib.ffi_add_many(k))
    assert py_calls_sum == ffi_calls_sum == one_call_sum
    print(f"  Per-call FFI vs Python fn: {ffi_calls_t/py_calls_t:.1f}x elapsed")
    print(f"  One FFI call vs {k:,} FFI calls: {ffi_calls_t / one_call_t:.1f}x elapsed (illustrative)")

    bench_queue(args.queue_size)
    print("\nInterpretation: move complete hot loops into native code; avoid one FFI call per literal/watch.")

if __name__ == "__main__":
    main()
