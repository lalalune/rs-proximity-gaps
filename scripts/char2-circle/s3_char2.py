"""
S3 — Characteristic 2 test.

FRI and Binius use F_{2^t}. The multiplicative group F_{2^t}* is cyclic of
order 2^t - 1 (odd). Take L = subgroup of order n | 2^t - 1.

Implement F_{2^t} arithmetic: elements as polynomials over F_2, mod an
irreducible polynomial of degree t. Multiplication via schoolbook + reduce.

Test the same questions:
1. CS finiteness: do non-aligned witnesses exist? At which fields?
2. List-size scaling: M = n/(t_agree - 1)?
3. MCA impossibility: does the degree argument hold in char 2?

Key difference from char p: no "prime p", instead we have F_{2^t}.
The n-th roots of unity ω satisfy ω^n = 1 in F_{2^t}*. The norm machinery
uses Z[ζ_n] with gcd(n, 2) = 1 (n is odd), so it should transfer.
"""

# F_{2^t} arithmetic using integer representation of polynomials over F_2
# Element a = a_0 + a_1*x + ... + a_{t-1}*x^{t-1} stored as integer (bit vector)

class GF2t:
    """Galois field F_{2^t} with a fixed irreducible polynomial."""

    def __init__(self, t, irr_poly=None):
        self.t = t
        self.q = 1 << t  # 2^t elements
        self.order = self.q - 1  # multiplicative group order
        if irr_poly is None:
            irr_poly = self._find_irreducible(t)
        self.irr = irr_poly
        # precompute log/exp tables for fast multiplication
        self._build_tables()

    def _find_irreducible(self, t):
        """Find an irreducible polynomial of degree t over F_2."""
        # Known irreducible polynomials (from AES, etc.)
        known = {
            4: 0b10011,       # x^4 + x + 1
            8: 0b100011011,   # x^8 + x^4 + x^3 + x + 1
            12: 0b1000001010011, # x^12 + x^6 + x^4 + x + 1 (verified irreducible)
            16: 0b10000000000101011, # x^16 + x^5 + x^3 + x + 1
        }
        if t in known:
            return known[t]
        # brute force search
        for p in range(1 << t | 1, (1 << (t+1)), 2):
            if self._is_irreducible(p, t):
                return p
        raise RuntimeError(f"no irreducible of degree {t}")

    def _is_irreducible(self, p, t):
        """Test if polynomial p (as integer) is irreducible over F_2."""
        # p is irreducible of degree t iff x^{2^t} = x mod p and
        # gcd(x^{2^k} - x, p) = 1 for k = 1, ..., t-1
        # Using polynomial GCD over F_2
        if self._poly_deg(p) != t: return False
        x = 2  # x as polynomial
        xpow = x
        for k in range(1, t):
            xpow = self._poly_powmod(xpow, 2, p)
            g = self._poly_gcd(xpow ^ x, p)
            if g != 1: return False
        xpow = self._poly_powmod(xpow, 2, p)
        return xpow == x

    def _poly_deg(self, a):
        if a == 0: return -1
        return a.bit_length() - 1

    def _poly_mod(self, a, m):
        dm = self._poly_deg(m)
        while True:
            da = self._poly_deg(a)
            if da < dm: return a
            a ^= m << (da - dm)

    def _poly_mulmod(self, a, b, m):
        result = 0
        while b:
            if b & 1: result ^= a
            a <<= 1
            b >>= 1
        return self._poly_mod(result, m)

    def _poly_powmod(self, base, exp, m):
        result = 1
        base = self._poly_mod(base, m)
        while exp > 0:
            if exp & 1: result = self._poly_mulmod(result, base, m)
            exp >>= 1
            base = self._poly_mulmod(base, base, m)
        return result

    def _poly_gcd(self, a, b):
        while b:
            a, b = b, self._poly_mod(a, b)
        return a

    def _build_tables(self):
        """Build exp/log tables using a generator of F_{2^t}*."""
        g = self._find_generator()
        self.exp_table = [0] * self.order
        self.log_table = [0] * self.q
        val = 1
        for i in range(self.order):
            self.exp_table[i] = val
            self.log_table[val] = i
            val = self._poly_mulmod(val, g, self.irr)
        self.generator = g

    def _find_generator(self):
        """Find a generator of F_{2^t}*."""
        from math import gcd
        order = self.order
        factors = set()
        n = order; d = 2
        while d * d <= n:
            while n % d == 0: factors.add(d); n //= d
            d += 1
        if n > 1: factors.add(n)

        for g in range(2, self.q):
            if all(self._poly_powmod(g, order // f, self.irr) != 1 for f in factors):
                return g
        raise RuntimeError

    def mul(self, a, b):
        if a == 0 or b == 0: return 0
        return self.exp_table[(self.log_table[a] + self.log_table[b]) % self.order]

    def inv(self, a):
        assert a != 0
        return self.exp_table[(self.order - self.log_table[a]) % self.order]

    def div(self, a, b):
        return self.mul(a, self.inv(b))

    def power(self, a, e):
        if a == 0: return 0
        return self.exp_table[(self.log_table[a] * e) % self.order]

    def add(self, a, b):
        return a ^ b  # F_2 addition = XOR

    def sub(self, a, b):
        return a ^ b  # same as add in char 2

    def omega(self, n):
        """Primitive n-th root of unity (n | 2^t - 1)."""
        assert self.order % n == 0
        return self.exp_table[self.order // n]


def prime_factors(n):
    out = set(); d = 2; nn = n
    while d * d <= nn:
        while nn % d == 0: out.add(d); nn //= d
        d += 1
    if nn > 1: out.add(nn)
    return list(out)

def divisors(n):
    return [d for d in range(1, n+1) if n % d == 0]

def cosets_of_index_subgroup(n, d):
    step = n // d; H = [(i * step) % n for i in range(d)]
    seen = set(); out = []
    for t in range(step):
        c = tuple(sorted((t + h) % n for h in H))
        if c not in seen: seen.add(c); out.append(c)
    return out

def is_subgroup_aligned(S_set, n):
    for d in divisors(n):
        if d == 1 or d == n: continue
        if len(S_set) % d != 0: continue
        cs = cosets_of_index_subgroup(n, d)
        covered = [c for c in cs if set(c).issubset(S_set)]
        if covered and sum(len(c) for c in covered) == len(S_set):
            return d
    return None

def test_char2(t_field, n, threshold=6):
    """Run the proximity gap tests in F_{2^t_field} with subgroup of order n."""
    F = GF2t(t_field)
    assert F.order % n == 0, f"n={n} does not divide 2^{t_field}-1={F.order}"

    w = F.omega(n)
    L = [F.power(w, i) for i in range(n)]

    print(f"  F_{{2^{t_field}}}, |F*|={F.order}, n={n}, (|F*|/n)={F.order//n}, omega={w}")

    # Test CS: w_lam(x) = x^6 + lam*x^4 for lam in F*
    # Also test (6,5) and (7,6)
    ab_pairs = [(6, 4), (6, 5), (7, 6)]

    for a, b in ab_pairs:
        max_M = 0
        max_M_not = 0
        total_wits = 0
        total_not = 0

        # sample lambda values
        lam_range = range(min(F.q, 100))
        for lam_idx in lam_range:
            lam = lam_idx  # elements of F as integers 0..q-1
            # w(x) = x^a + lam*x^b for x in L
            w_vals = [F.add(F.power(L[i], a), F.mul(lam, F.power(L[i], b))) for i in range(n)]

            # Lagrange trick for k=2
            seen_h = {}
            this_M = 0
            this_not = 0
            for i in range(n):
                for j in range(i+1, n):
                    dx = F.sub(L[i], L[j])
                    dy = F.sub(w_vals[i], w_vals[j])
                    if dx == 0: continue
                    h1 = F.div(dy, dx)
                    h0 = F.sub(w_vals[i], F.mul(h1, L[i]))
                    key = (h0, h1)
                    if key in seen_h: continue
                    agree = set()
                    for idx in range(n):
                        if F.add(h0, F.mul(h1, L[idx])) == w_vals[idx]:
                            agree.add(idx)
                    seen_h[key] = len(agree)
                    if len(agree) >= threshold:
                        this_M += 1
                        total_wits += 1
                        if is_subgroup_aligned(agree, n) is None:
                            this_not += 1
                            total_not += 1

            max_M = max(max_M, this_M)
            max_M_not = max(max_M_not, this_not)

        print(f"    ({a},{b}): max_M={max_M}, max_NOT={max_M_not}, total={total_wits}, NOT={total_not}, "
              f"n/{threshold-1}={n/(threshold-1):.1f}")

def main():
    threshold = 6
    print(f"=== S3: Characteristic 2 test ===")
    print(f"threshold t_agree={threshold}\n")

    # F_{2^8}: 2^8 - 1 = 255 = 3 * 5 * 17
    # Subgroups of order: 3, 5, 15, 17, 51, 85
    print("--- F_{2^8}, |F*| = 255 ---")
    for n in [15, 17, 51, 85]:
        if 255 % n != 0: continue
        if n < threshold: continue
        print(f"  n={n}:")
        test_char2(8, n, threshold)

    # F_{2^12}: 2^12 - 1 = 4095 = 3^2 * 5 * 7 * 13
    # Subgroups: 7, 9, 13, 21, 35, 45, 63, 65, 91, 105, ...
    print("\n--- F_{2^12}, |F*| = 4095 ---")
    for n in [13, 21, 35, 45, 63, 65, 91]:
        if 4095 % n != 0: continue
        if n < threshold: continue
        print(f"  n={n}:")
        test_char2(12, n, threshold)

    # F_{2^16}: 2^16 - 1 = 65535 = 3 * 5 * 17 * 257
    print("\n--- F_{2^16}, |F*| = 65535 ---")
    for n in [15, 17, 51, 85, 255, 257]:
        if 65535 % n != 0: continue
        if n < threshold: continue
        print(f"  n={n}:")
        test_char2(16, n, threshold)

if __name__ == "__main__":
    main()
