"""
FRI Folding — minimal, focused on n=8,10 with precomputed tables.
"""
import math, random
from itertools import product as iprod
from collections import Counter

def find_params(n):
    p = n + 1
    while True:
        if p % n == 1:
            ok = True
            for i in range(2, int(p**0.5)+1):
                if p % i == 0: ok = False; break
            if ok:
                for g in range(2, p):
                    x, seen = 1, set()
                    for _ in range(p-1): seen.add(x); x = x*g%p
                    if len(seen) == p-1:
                        return p, pow(g, (p-1)//n, p)
        p += n

def run(n, k):
    p, omega = find_params(n)
    w = int(math.floor((1 - math.sqrt(k/n)) * n))
    if w < 1: w = 1
    n2, k2 = n//2, (k + 1)//2
    w2 = int(math.floor((1 - math.sqrt(k2/n2)) * n2))
    if w2 < 1: w2 = 1

    print(f"\n{'='*60}")
    print(f"n={n} k={k} p={p} w={w} | n'={n2} k'={k2} w'={w2}")
    print(f"{'='*60}")

    # Precompute evaluation table: powers[i] = omega^i
    pw = [pow(omega, i, p) for i in range(n)]
    pw2 = [pow(omega, 2*i, p) for i in range(n2)]
    inv2 = pow(2, p-2, p)

    # Build ALL codewords as value vectors
    print(f"Building {p}^{k} = {p**k} codewords...", flush=True)
    all_cws = []  # (coeffs, vals)
    for ct in iprod(range(p), repeat=k):
        vals = []
        for i in range(n):
            v = 0; xi = 1
            for c in ct:
                v = (v + c*xi) % p
                xi = xi * pw[i] % p
            vals.append(v)
        all_cws.append((list(ct), vals))
    print(f"  Done: {len(all_cws)} codewords")

    # Find centers with largest M
    random.seed(42)
    best_M, best_data = 0, None

    n_trials = 300
    for trial in range(n_trials):
        center = [random.randrange(p) for _ in range(n)]
        close = []
        for coeffs, vals in all_cws:
            d = sum(1 for a,b in zip(vals, center) if (a-b)%p)
            if d <= w:
                close.append((coeffs, vals, d))
        if len(close) > best_M:
            best_M = len(close)
            best_data = (center, close)

    print(f"Max M = {best_M} over {n_trials} centers")
    if best_M == 0:
        print("No close codewords found.")
        return

    center, cws = best_data

    # Error pairing analysis
    print(f"\nError pairing:")
    for idx, (co, va, d) in enumerate(cws):
        E = {i for i in range(n) if (va[i]-center[i])%p}
        n_half = n//2
        paired = sum(1 for i in E if (i+n_half)%n in E) // 2
        unp = len(E) - 2*paired
        print(f"  cw{idx}: d={d} E={sorted(E)} paired={paired} unp={unp}")

    # FRI folding with many alpha values
    print(f"\nFolding survival (p-1={p-1} alpha values):")
    all_survive_counts = []

    for alpha in range(1, p):
        # Fold center
        gc = []
        for i in range(n2):
            fi, fi2 = center[i], center[i+n2]
            fe = (fi + fi2) * inv2 % p
            inv_oi = pow(pw[i], p-2, p)
            fo = (fi - fi2) * inv2 % p * inv_oi % p
            gc.append((fe + alpha*fo) % p)

        # Fold each codeword and check distance
        surv = 0
        for co, va, d in cws:
            # Fold coefficients
            fc = [(co[2*j] + alpha * co[2*j+1]) % p if 2*j+1 < k
                  else co[2*j] for j in range(k2)]
            # Evaluate folded codeword on L'
            fv = []
            for i in range(n2):
                v = 0; xi = 1
                for c in fc:
                    v = (v + c*xi) % p
                    xi = xi * pw2[i] % p
                fv.append(v)
            df = sum(1 for a,b in zip(fv, gc) if (a-b)%p)
            if df <= w2:
                surv += 1
        all_survive_counts.append(surv)

    dist = Counter(all_survive_counts)
    print(f"  Original M = {best_M}")
    print(f"  Folded M' distribution over all {p-1} alpha: {dict(sorted(dist.items()))}")
    print(f"  Mean M' = {sum(all_survive_counts)/len(all_survive_counts):.3f}")
    print(f"  Max M' = {max(all_survive_counts)}")
    print(f"  # alpha with M'=0: {all_survive_counts.count(0)}")

    # Show which codewords survive for each alpha (if M is small)
    if best_M <= 8:
        print(f"\n  Per-codeword survival fraction:")
        for idx, (co, va, d) in enumerate(cws):
            count = 0
            for alpha in range(1, p):
                gc2 = []
                for i in range(n2):
                    fi, fi2 = center[i], center[i+n2]
                    fe = (fi + fi2) * inv2 % p
                    inv_oi = pow(pw[i], p-2, p)
                    fo = (fi - fi2) * inv2 % p * inv_oi % p
                    gc2.append((fe + alpha*fo) % p)

                fc = [(co[2*j] + alpha * co[2*j+1]) % p if 2*j+1 < k
                      else co[2*j] for j in range(k2)]
                fv = []
                for i2 in range(n2):
                    v = 0; xi = 1
                    for c in fc:
                        v = (v + c*xi) % p
                        xi = xi * pw2[i2] % p
                    fv.append(v)
                df = sum(1 for a,b in zip(fv, gc2) if (a-b)%p)
                if df <= w2:
                    count += 1

            E = {i for i in range(n) if (va[i]-center[i])%p}
            paired = sum(1 for i in E if (i+n//2)%n in E) // 2
            unp = len(E) - 2*paired
            print(f"    cw{idx}: d={d} p={paired} u={unp} "
                  f"survive={count}/{p-1} ({100*count/(p-1):.1f}%)")

    # Multi-round folding
    print(f"\n  Multi-round folding (10 random alpha sequences):")
    random.seed(123)
    for trial in range(10):
        cur_c = center[:]
        cur_list = [(co[:], va[:], d) for co, va, d in cws]
        cur_n, cur_k = n, k
        cur_om = omega
        chain = [len(cur_list)]

        while cur_n >= 4 and cur_k >= 2 and len(cur_list) > 0:
            al = random.randrange(1, p)
            nn, nk = cur_n//2, (cur_k + 1)//2
            if nk < 1: break
            nw = int(math.floor((1-math.sqrt(nk/nn))*nn))
            if nw < 1: nw = 1
            inv2_ = pow(2, p-2, p)
            nom = pow(cur_om, 2, p)
            npw = [pow(nom, i, p) for i in range(nn)]

            nc = []
            for i in range(nn):
                fi, fi2 = cur_c[i], cur_c[i+nn]
                fe = (fi + fi2)*inv2_%p
                inv_oi = pow(pow(cur_om, i, p), p-2, p)
                fo = (fi - fi2)*inv2_%p * inv_oi%p
                nc.append((fe + al*fo)%p)

            nl = []
            for co, va, d in cur_list:
                fc2 = [(co[2*j]+al*co[2*j+1])%p if 2*j+1<cur_k
                       else co[2*j] for j in range(nk)]
                fv2 = []
                for i2 in range(nn):
                    v = 0; xi = 1
                    for c in fc2:
                        v = (v+c*xi)%p; xi = xi*npw[i2]%p
                    fv2.append(v)
                df2 = sum(1 for a,b in zip(fv2, nc) if (a-b)%p)
                if df2 <= nw:
                    nl.append((fc2, fv2, df2))

            cur_c, cur_list = nc, nl
            cur_n, cur_k, cur_om = nn, nk, nom
            chain.append(len(cur_list))

        print(f"    trial {trial}: M chain = {chain}")


# Run
run(8, 4)
run(10, 5)
