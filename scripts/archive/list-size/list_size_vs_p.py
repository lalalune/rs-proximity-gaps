"""
List size M as a function of p (field size), for fixed n, k, delta.
Goal: confirm M → 0 as p → ∞.
"""
import random, math
from itertools import combinations

def find_prim_root(p, n):
    assert (p - 1) % n == 0
    for g in range(2, p):
        w = pow(g, (p - 1) // n, p)
        if pow(w, n, p) == 1:
            ok = True
            temp = n
            d = 2
            while d * d <= temp:
                while temp % d == 0:
                    if pow(w, n // d, p) == 1: ok = False
                    temp //= d
                d += 1
            if temp > 1 and pow(w, n // temp, p) == 1: ok = False
            if ok: return w
    return None

def modinv(a, p): return pow(a, p - 2, p)

def solve_system(H_T, syndromes, p):
    m = len(H_T); nv = len(H_T[0]) if m > 0 else 0
    aug = [row[:] + [syndromes[i]] for i, row in enumerate(H_T)]
    pc = 0; pivots = []
    for row in range(m):
        if pc >= nv: break
        found = -1
        for r in range(row, m):
            if aug[r][pc] % p != 0: found = r; break
        if found == -1: pc += 1; continue
        aug[row], aug[found] = aug[found], aug[row]
        inv = modinv(aug[row][pc], p)
        aug[row] = [(x * inv) % p for x in aug[row]]
        for r in range(m):
            if r != row and aug[r][pc] % p != 0:
                f = aug[r][pc]
                aug[r] = [(aug[r][j] - f * aug[row][j]) % p for j in range(nv + 1)]
        pivots.append((row, pc)); pc += 1
    for r in range(len(pivots), m):
        if aug[r][nv] % p != 0: return None
    x = [0] * nv
    for row, col in pivots: x[col] = aug[row][nv] % p
    return x

def count_list_size(n, k, p, delta, num_words=5):
    omega = find_prim_root(p, n)
    if omega is None: return -1
    L = [pow(omega, i, p) for i in range(n)]
    t = int((1 - delta) * n)
    max_err = n - t
    omega_inv = modinv(omega, p)

    max_M = 0
    for _ in range(num_words):
        w_vals = [random.randint(0, p-1) for _ in range(n)]
        syndromes = []
        for j in range(k, n):
            s = sum(w_vals[i] * pow(omega_inv, i*j, p) for i in range(n)) % p
            syndromes.append(s)

        M = 0
        for w_err in range(1, max_err + 1):
            if math.comb(n, w_err) > 200000: break
            for T in combinations(range(n), w_err):
                H_T = [[pow(omega_inv, (r+k)*i, p) for i in T] for r in range(n-k)]
                sol = solve_system(H_T, syndromes, p)
                if sol is not None and all(s % p != 0 for s in sol):
                    M += 1
        # Check w=0 (w is a codeword)
        if all(s % p == 0 for s in syndromes): M += 1
        max_M = max(max_M, M)
    return max_M

random.seed(42)

# Fixed n=12, k=6 (rate 1/2), delta=0.35
# Vary p across primes where 12 | (p-1)
print("n=12, k=6, delta=0.35 (above Johnson 0.293)")
print(f"{'p':>6} {'p/n':>6} {'M_max':>8} {'heuristic':>12}")
print("-" * 40)

for p in [13, 37, 61, 97, 109, 157, 181, 229, 277, 349, 397, 433, 541, 661, 769, 997]:
    if (p - 1) % 12 != 0: continue
    if not all(p % i != 0 for i in range(2, int(p**0.5)+1)): continue
    M = count_list_size(12, 6, p, 0.35, num_words=10)
    # Heuristic: sum over w=1..4 of C(12,w)*(p-1)^w / p^6
    heur = sum(math.comb(12, w) * (p-1)**w / p**6 for w in range(1, 5))
    print(f"{p:6d} {p/12:6.1f} {M:8d} {heur:12.4f}")

print()

# Fixed n=16, k=8 (rate 1/2), delta=0.35
print("n=16, k=8, delta=0.35 (above Johnson 0.293)")
print(f"{'p':>6} {'p/n':>6} {'M_max':>8} {'heuristic':>12}")
print("-" * 40)

for p in [17, 97, 193, 257, 337, 433, 577, 769, 929]:
    if (p - 1) % 16 != 0: continue
    if not all(p % i != 0 for i in range(2, int(p**0.5)+1)): continue
    M = count_list_size(16, 8, p, 0.35, num_words=5)
    heur = sum(math.comb(16, w) * (p-1)**w / p**8 for w in range(1, 11))
    print(f"{p:6d} {p/16:6.1f} {M:8d} {heur:12.6f}")
