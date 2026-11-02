#include <cstdint>

// C ABI makes C++ functions callable using Python ctypes.
extern "C" {

int64_t ffi_add_one(int64_t x) {
    return x + 1;
}

// A toy SAT-like literal evaluation kernel; NOT a CDCL propagation engine.
// values[v] is 0=false, 1=true; index 0 unused.
// Each repetition rotates the literal traversal to vary access order.
// The returned checksum makes it possible to verify equivalent work.
int64_t ffi_count_satisfied(
    const int32_t* lits, const int8_t* values,
    int32_t n, int32_t repeats
) {
    if (n <= 0 || repeats <= 0) return 0;
    int64_t satisfied = 0;
    for (int32_t r = 0; r < repeats; ++r) {
        int32_t index = r % n;
        for (int32_t j = 0; j < n; ++j) {
            const int32_t lit = lits[index];
            const int32_t var = lit > 0 ? lit : -lit;
            const int8_t val = values[var];
            if ((lit > 0 && val == 1) || (lit < 0 && val == 0)) {
                ++satisfied;
            }
            if (++index == n) index = 0;
        }
    }
    return satisfied;
}

// Illustrates batching tiny computations into one native call.
int64_t ffi_add_many(int32_t count) {
    int64_t sum = 0;
    for (int32_t i = 0; i < count; ++i) {
        sum += ffi_add_one(i);
    }
    return sum;
}
}
