#!/usr/bin/env python3
"""Deterministic verifier for the reduced-round product-model searches in
'Inner c-Differential Cryptanalysis of Kuznyechik'.

No random sampling is used.  The script reconstructs the Kuznyechik S-box
DDT and inner-c tables, the RFC 7801 L transformation, and exhaustively
checks:
  * post-L1 weight-one two-round search (16*255 boundaries),
  * the 16->1->16 three-round family,
  * all C(16,2)*255^2 = 7,803,000 post-L1 weight-two boundaries,
  * the 16->1->16->1 four-round family.

Scores are exact product-model log2 probabilities: every local transition
with count d contributes log2(d/256), with no integer rounding.
"""

from __future__ import annotations
import math
import itertools
import numpy as np

SBOX = np.array([
252,238,221,17,207,110,49,22,251,196,250,218,35,197,4,77,
233,119,240,219,147,46,153,186,23,54,241,187,20,205,95,193,
249,24,101,90,226,92,239,33,129,28,60,66,139,1,142,79,
5,132,2,174,227,106,143,160,6,11,237,152,127,212,211,31,
235,52,44,81,234,200,72,171,242,42,104,162,253,58,206,204,
181,112,14,86,8,12,118,18,191,114,19,71,156,183,93,135,
21,161,150,41,16,123,154,199,243,145,120,111,157,158,178,177,
50,117,25,61,255,53,138,126,109,84,198,128,195,189,13,87,
223,245,36,169,62,168,67,201,215,121,214,246,124,34,185,3,
224,15,236,222,122,148,176,188,220,232,40,80,78,51,10,74,
167,151,96,115,30,0,98,68,26,184,56,130,100,159,38,65,
173,69,70,146,39,94,85,47,140,163,165,125,105,213,149,59,
7,88,179,64,134,172,29,247,48,55,107,228,136,217,231,137,
225,27,131,73,76,63,248,254,141,83,170,144,202,216,133,97,
32,113,103,164,45,43,9,91,203,155,37,208,190,229,108,82,
89,166,116,210,230,244,180,192,209,102,175,194,57,75,99,182
], dtype=np.uint8)

L_CONST = (148,32,133,16,194,192,1,251,1,192,194,16,133,32,148,1)
CS = (0x01, 0x02, 0xE1, 0x04, 0x03)


def gf_mul(a: int, b: int) -> int:
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        hi = a & 0x80
        a = (a << 1) & 0xFF
        if hi:
            a ^= 0xC3
        b >>= 1
    return p


def R(state):
    z = 0
    for x, c in zip(state, L_CONST):
        z ^= gf_mul(int(x), c)
    return [z] + list(state[:-1])


def Rinv(state):
    x = list(state[1:]) + [0]
    z = int(state[0])
    for i in range(15):
        z ^= gf_mul(int(x[i]), L_CONST[i])
    x[15] = z  # last L coefficient is 1
    return x


def L(state):
    x = list(state)
    for _ in range(16):
        x = R(x)
    return x


def Linv(state):
    x = list(state)
    for _ in range(16):
        x = Rinv(x)
    return x


def build_ddt():
    ddt = np.zeros((256,256), dtype=np.int16)
    for a in range(256):
        for x in range(256):
            ddt[a, int(SBOX[x]) ^ int(SBOX[x ^ a])] += 1
    return ddt


def build_inner(c: int):
    tab = np.zeros((256,256), dtype=np.int16)
    for a in range(256):
        for x in range(256):
            y = gf_mul(c, x) ^ a
            tab[a, int(SBOX[y]) ^ int(SBOX[x])] += 1
    return tab


def cost_from_count(d):
    if d <= 0:
        return math.inf
    return 8.0 - math.log2(float(d))


def main():
    ddt = build_ddt()
    dstar = ddt.max(axis=1).astype(np.int16)
    dcost = np.array([cost_from_count(int(x)) for x in dstar], dtype=float)

    inner = {1: ddt}
    for c in CS:
        if c != 1:
            inner[c] = build_inner(c)
    mstar = {c: inner[c][1:,:].max(axis=0).astype(np.int16) for c in CS}
    mcost = {c: np.array([cost_from_count(int(x)) for x in mstar[c]], dtype=float) for c in CS}

    # Linear images of all one-byte values; byte ordering follows RFC implementation.
    invbasis = np.zeros((16,256,16), dtype=np.uint8)
    lbasis = np.zeros((16,256,16), dtype=np.uint8)
    for p in range(16):
        for a in range(1,256):
            v = [0]*16; v[p] = a
            invbasis[p,a] = np.array(Linv(v), dtype=np.uint8)
            lbasis[p,a] = np.array(L(v), dtype=np.uint8)

    print("Kuznyechik reduced-round deterministic verification")
    print("====================================================")
    print("No RNG is used. All reported families are exhaustively enumerated.\n")

    # 2 rounds, post-L1 weight one.
    best2 = {}
    first_cache = {c: np.full((16,256), np.inf) for c in CS}
    first_counts = {c: {} for c in CS}
    for c in CS:
        best = (math.inf, None)
        for k in range(16):
            for beta in range(1,256):
                delta = invbasis[k,beta]
                cnts = mstar[c][delta]
                if np.any(cnts == 0):
                    continue
                c1 = float(mcost[c][delta].sum())
                first_cache[c][k,beta] = c1
                c2 = float(dcost[beta])
                total = c1 + c2
                if total < best[0]:
                    best = (total, (k,beta,c1,c2,[int(x) for x in cnts]))
        best2[c] = best

    print("Two rounds, post-L1 weight one")
    for c in CS:
        total,(k,beta,c1,c2,cnts)=best2[c]
        print(f"c={c:02x}: exponent {total:.10f}; k={k}, beta={beta:02x}; "
              f"round costs {c1:.10f}+{c2:.10f}")
        print("       first-layer counts:", tuple(cnts))
    print()

    # 3 rounds: 16 -> 1 -> 16. Third round is optimized coordinatewise.
    third_cost = np.full((16,256), np.inf)
    third_counts = {}
    for k in range(16):
        for gamma in range(1,256):
            inp = lbasis[k,gamma]
            cnts = dstar[inp]
            if np.any(cnts == 0):
                continue
            third_cost[k,gamma] = float(dcost[inp].sum())
            third_counts[(k,gamma)] = tuple(int(x) for x in cnts)

    best3 = {}
    for c in CS:
        best = (math.inf,None)
        for k in range(16):
            for beta in range(1,256):
                c1 = first_cache[c][k,beta]
                if not math.isfinite(c1):
                    continue
                for gamma in np.flatnonzero(ddt[beta]):
                    gamma = int(gamma)
                    if gamma == 0 or not math.isfinite(third_cost[k,gamma]):
                        continue
                    c2 = cost_from_count(int(ddt[beta,gamma]))
                    c3 = float(third_cost[k,gamma])
                    total = c1+c2+c3
                    if total < best[0]:
                        best=(total,(k,beta,gamma,c1,c2,c3,third_counts[(k,gamma)]))
        best3[c]=best

    print("Three rounds, 16 -> 1 -> 16")
    for c in CS:
        total,(k,beta,gamma,c1,c2,c3,cnts3)=best3[c]
        print(f"c={c:02x}: exponent {total:.10f}; k={k}, beta={beta:02x}, gamma={gamma:02x}; "
              f"round costs {c1:.10f}+{c2:.10f}+{c3:.10f}")
        if c in (1,2): print("       third-layer counts:", cnts3)
    print()

    # Exhaustive post-L1 weight two, vectorized over the 255^2 byte values for each pair of positions.
    bestw2 = {c:(math.inf,None) for c in CS}
    boundary_count = 0
    vals = np.arange(1,256,dtype=np.int16)
    second2 = dcost[1:,None] + dcost[None,1:]
    for p,q in itertools.combinations(range(16),2):
        delta = np.bitwise_xor(invbasis[p,1:,None,:], invbasis[q,None,1:,:])  # 255x255x16
        boundary_count += 255*255
        for c in CS:
            costs = mcost[c][delta].sum(axis=2) + second2
            flat = int(np.argmin(costs))
            value = float(costs.reshape(-1)[flat])
            if value < bestw2[c][0]:
                ia,ib = np.unravel_index(flat,(255,255))
                bestw2[c]=(value,(p,q,int(vals[ia]),int(vals[ib])))

    print(f"Post-L1 weight two: exhaustively checked {boundary_count:,} boundaries")
    for c in CS:
        total,(p,q,a,b)=bestw2[c]
        print(f"c={c:02x}: exponent {total:.10f}; positions=({p},{q}), values=({a:02x},{b:02x})")
    print()

    # 4 rounds: 16 -> 1 -> 16 -> 1.
    # For each (k,gamma), exhaustively optimize the third-round S-box output over every
    # weight-one post-L3 boundary (h,delta), then add the best fourth S-box transition.
    out3_all = invbasis[:,1:,:].reshape(16*255,16)
    labels_h = np.repeat(np.arange(16),255)
    labels_delta = np.tile(np.arange(1,256),16)
    fourth_cost_all = dcost[labels_delta]
    cont = np.full((16,256),np.inf)
    cont_arg = {}
    for k in range(16):
        for gamma in range(1,256):
            inp3 = lbasis[k,gamma]
            cnt = ddt[inp3[None,:], out3_all]  # 4080 x 16
            valid = np.all(cnt > 0, axis=1)
            if not np.any(valid):
                continue
            local = np.full(16*255,np.inf)
            # exact log costs for valid candidates
            cmat = 8.0 - np.log2(cnt[valid].astype(float))
            local[valid] = cmat.sum(axis=1) + fourth_cost_all[valid]
            idx = int(np.argmin(local))
            cont[k,gamma] = float(local[idx])
            cont_arg[(k,gamma)] = (int(labels_h[idx]),int(labels_delta[idx]),
                                    tuple(int(x) for x in cnt[idx]))

    best4 = {}
    for c in CS:
        best=(math.inf,None)
        for k in range(16):
            for beta in range(1,256):
                c1=first_cache[c][k,beta]
                if not math.isfinite(c1): continue
                for gamma in np.flatnonzero(ddt[beta]):
                    gamma=int(gamma)
                    if gamma==0 or not math.isfinite(cont[k,gamma]): continue
                    c2=cost_from_count(int(ddt[beta,gamma]))
                    total=c1+c2+float(cont[k,gamma])
                    if total<best[0]:
                        h,delta,cnts3=cont_arg[(k,gamma)]
                        c4=cost_from_count(int(dstar[delta]))
                        c3=float(cont[k,gamma])-c4
                        best=(total,(k,beta,gamma,h,delta,c1,c2,c3,c4,cnts3))
        best4[c]=best

    print("Four rounds, 16 -> 1 -> 16 -> 1 (exhaustive within this topology)")
    for c in CS:
        total,(k,beta,gamma,h,delta,c1,c2,c3,c4,cnts3)=best4[c]
        print(f"c={c:02x}: exponent {total:.10f}; k={k}, beta={beta:02x}, gamma={gamma:02x}, "
              f"next-pos={h}, delta={delta:02x}; costs "
              f"{c1:.10f}+{c2:.10f}+{c3:.10f}+{c4:.10f}")
        if c in (1,2): print("       third-layer counts:", cnts3)
    print()

    # Regression assertions for manuscript values that were independently reconstructed exactly.
    expected2={1:89.15037499278843,2:83.98012019478716,0xe1:83.98012019478716,4:89.98143742960445,3:91.19548534922964}
    expected3={1:174.30074998557689,2:169.71545768829674,0xe1:169.71545768829674,3:177.34586034201809}
    expectedw2={1:93.3202999942,2:85.9983718993,0xe1:85.9983718993,4:90.5738722331,3:94.0479506277}
    for c,v in expected2.items(): assert abs(best2[c][0]-v)<1e-9
    for c,v in expected3.items(): assert abs(best3[c][0]-v)<1e-9
    for c,v in expectedw2.items(): assert abs(bestw2[c][0]-v)<1e-8
    print("Regression assertions: PASS")
    print("Note: the exhaustive four-round values differ from the older manuscript values 202.7/202.8;")
    print("the values printed above are the reconstructed optima for the stated topology.")

if __name__ == "__main__":
    main()
