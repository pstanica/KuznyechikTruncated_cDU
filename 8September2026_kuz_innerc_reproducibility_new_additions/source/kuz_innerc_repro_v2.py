#!/usr/bin/env python3
"""Exact reproducibility code for inner-c analysis of Kuznyechik's S-box.

What it computes
----------------
1. Ordinary DDT and full inner-c tables N_c(a,b) in the public Kuznyechik field.
2. delta_c, full-table energy E_c, Pearson-information parameter E_c/2^16-1,
   and I(K;B) for the one-byte whitening-key channel.
3. Perrin/Udovenko hidden-field multiplicative transitions, cross-field
   disagreement ranks, exact fiber splits, and transfer lower bounds.
4. Whole-spectrum transfer-score B(c) and correlation with actual delta_c.
5. Exact standard-prewhitening weak-key byte classes.
6. An exact two-round, one-byte-output profile
       Q(a) = 2^-16 sum_b N_c(a,b) DDT[lambda*b, gamma],
   together with a weak-key density/probability tradeoff for c=0x02.
7. RFC 7801 R/L regression tests and optional Monte-Carlo validation.

Byte indexing is 0..15 from left to right in the RFC hexadecimal state.

Dependencies: Python 3, numpy. scipy is optional (only for power calculations).
"""
from __future__ import annotations
import argparse, csv, json, math
from fractions import Fraction
from pathlib import Path
import numpy as np

SBOX = np.array([
0xFC,0xEE,0xDD,0x11,0xCF,0x6E,0x31,0x16,0xFB,0xC4,0xFA,0xDA,0x23,0xC5,0x04,0x4D,
0xE9,0x77,0xF0,0xDB,0x93,0x2E,0x99,0xBA,0x17,0x36,0xF1,0xBB,0x14,0xCD,0x5F,0xC1,
0xF9,0x18,0x65,0x5A,0xE2,0x5C,0xEF,0x21,0x81,0x1C,0x3C,0x42,0x8B,0x01,0x8E,0x4F,
0x05,0x84,0x02,0xAE,0xE3,0x6A,0x8F,0xA0,0x06,0x0B,0xED,0x98,0x7F,0xD4,0xD3,0x1F,
0xEB,0x34,0x2C,0x51,0xEA,0xC8,0x48,0xAB,0xF2,0x2A,0x68,0xA2,0xFD,0x3A,0xCE,0xCC,
0xB5,0x70,0x0E,0x56,0x08,0x0C,0x76,0x12,0xBF,0x72,0x13,0x47,0x9C,0xB7,0x5D,0x87,
0x15,0xA1,0x96,0x29,0x10,0x7B,0x9A,0xC7,0xF3,0x91,0x78,0x6F,0x9D,0x9E,0xB2,0xB1,
0x32,0x75,0x19,0x3D,0xFF,0x35,0x8A,0x7E,0x6D,0x54,0xC6,0x80,0xC3,0xBD,0x0D,0x57,
0xDF,0xF5,0x24,0xA9,0x3E,0xA8,0x43,0xC9,0xD7,0x79,0xD6,0xF6,0x7C,0x22,0xB9,0x03,
0xE0,0x0F,0xEC,0xDE,0x7A,0x94,0xB0,0xBC,0xDC,0xE8,0x28,0x50,0x4E,0x33,0x0A,0x4A,
0xA7,0x97,0x60,0x73,0x1E,0x00,0x62,0x44,0x1A,0xB8,0x38,0x82,0x64,0x9F,0x26,0x41,
0xAD,0x45,0x46,0x92,0x27,0x5E,0x55,0x2F,0x8C,0xA3,0xA5,0x7D,0x69,0xD5,0x95,0x3B,
0x07,0x58,0xB3,0x40,0x86,0xAC,0x1D,0xF7,0x30,0x37,0x6B,0xE4,0x88,0xD9,0xE7,0x89,
0xE1,0x1B,0x83,0x49,0x4C,0x3F,0xF8,0xFE,0x8D,0x53,0xAA,0x90,0xCA,0xD8,0x85,0x61,
0x20,0x71,0x67,0xA4,0x2D,0x2B,0x09,0x5B,0xCB,0x9B,0x25,0xD0,0xBE,0xE5,0x6C,0x52,
0x59,0xA6,0x74,0xD2,0xE6,0xF4,0xB4,0xC0,0xD1,0x66,0xAF,0xC2,0x39,0x4B,0x63,0xB6
], dtype=np.uint8)

PUBLIC_POLY = 0x1C3  # x^8+x^7+x^6+x+1
HIDDEN_POLY = 0x11D  # x^8+x^4+x^3+x^2+1 (Perrin/Udovenko field)
R_COEFF = [0x94,0x20,0x85,0x10,0xC2,0xC0,0x01,0xFB,
           0x01,0xC0,0xC2,0x10,0x85,0x20,0x94,0x01]
Q = 256
X = np.arange(256, dtype=np.uint16)


def gf_mul(a: int, b: int, poly: int) -> int:
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a & 0x100:
            a ^= poly
    return r & 0xFF


def make_mul_table(poly: int) -> np.ndarray:
    T = np.zeros((256,256), dtype=np.uint8)
    for a in range(256):
        for b in range(256):
            T[a,b] = gf_mul(a,b,poly)
    return T


MP = make_mul_table(PUBLIC_POLY)
MH = make_mul_table(HIDDEN_POLY)


def gf_inv(a: int, table: np.ndarray = MP) -> int:
    if a == 0:
        raise ZeroDivisionError
    for x in range(1,256):
        if int(table[a,x]) == 1:
            return x
    raise RuntimeError("no inverse")


def ordinary_ddt() -> np.ndarray:
    D = np.zeros((256,256), dtype=np.uint16)
    sx = SBOX[X]
    for a in range(256):
        y = np.bitwise_xor(SBOX[np.bitwise_xor(X,a)], sx)
        D[a] = np.bincount(y, minlength=256)
    return D


DDT = ordinary_ddt()


def inner_table(c: int) -> np.ndarray:
    """N_c(a,b) = #{x: S(c*x + a)+S(x)=b}, multiplication in public field."""
    cx = MP[c].astype(np.uint16)
    sx = SBOX[X]
    N = np.zeros((256,256), dtype=np.uint16)
    for a in range(256):
        y = np.bitwise_xor(SBOX[np.bitwise_xor(cx,a)], sx)
        N[a] = np.bincount(y, minlength=256)
    return N


def inner_metrics(N: np.ndarray) -> dict:
    E = int(np.sum(N.astype(np.int64)**2))
    nz = N[N > 0].astype(np.float64)
    return {
        "delta_full": int(N.max()),
        "energy": E,
        "pearson_key_output": E / 65536.0 - 1.0,
        "mutual_information_bits": float(np.sum(nz*np.log2(nz))/65536.0),
    }


def hidden_hist(lam: int) -> np.ndarray:
    y = np.bitwise_xor(SBOX[MH[lam].astype(np.uint16)], SBOX[X])
    return np.bincount(y, minlength=256).astype(np.uint16)


def multiplication_columns(c: int, table: np.ndarray) -> list[int]:
    return [int(table[c,1 << j]) for j in range(8)]


def binary_rank_from_columns(cols: list[int]) -> int:
    rows = []
    for i in range(8):
        row = 0
        for j, col in enumerate(cols):
            if (col >> i) & 1:
                row |= 1 << j
        rows.append(row)
    rank = 0
    for bit in range(7,-1,-1):
        pivot = next((i for i in range(rank,8) if (rows[i] >> bit) & 1), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for i in range(8):
            if i != rank and ((rows[i] >> bit) & 1):
                rows[i] ^= rows[rank]
        rank += 1
    return rank


def disagreement_rank(c_public: int, lam_hidden: int) -> int:
    cp = multiplication_columns(c_public, MP)
    ch = multiplication_columns(lam_hidden, MH)
    return binary_rank_from_columns([a ^ b for a,b in zip(cp,ch)])


def transfer_fibers(c_public: int, lam_hidden: int, b: int) -> dict[int,int]:
    fibers: dict[int,int] = {}
    for x in range(256):
        if (int(SBOX[int(MH[lam_hidden,x])]) ^ int(SBOX[x])) == b:
            a = int(MP[c_public,x]) ^ int(MH[lam_hidden,x])
            fibers[a] = fibers.get(a,0) + 1
    return fibers


def sharp_integer_energy_lower(h: int, r: int) -> int:
    m = 1 << r
    q0, s = divmod(h,m)
    return s*(q0+1)**2 + (m-s)*q0**2


def R(state: list[int]) -> list[int]:
    z = 0
    for a,c in zip(state,R_COEFF):
        z ^= gf_mul(a,c,PUBLIC_POLY)
    return [z] + state[:15]


def R_inv(state: list[int]) -> list[int]:
    # R(a15,...,a0)=(ell(a),a15,...,a1), coefficient of a0 is 1.
    known = state[1:]
    a0 = state[0]
    for a,c in zip(known,R_COEFF[:15]):
        a0 ^= gf_mul(a,c,PUBLIC_POLY)
    return known + [a0]


def L(state: list[int]) -> list[int]:
    s = list(state)
    for _ in range(16):
        s = R(s)
    return s


def L_inv(state: list[int]) -> list[int]:
    s = list(state)
    for _ in range(16):
        s = R_inv(s)
    return s


def rfc_regression_tests() -> None:
    r_in = list(bytes.fromhex('00000000000000000000000000000100'))
    r_out = bytes(R(r_in)).hex()
    assert r_out == '94000000000000000000000000000001', r_out
    l_in = list(bytes.fromhex('64a59400000000000000000000000000'))
    l_out = bytes(L(l_in)).hex()
    assert l_out == 'd456584dd0e3e84cc3166e4b7fa2890d', l_out
    assert L_inv(L(l_in)) == l_in


def L_matrix() -> np.ndarray:
    M = np.zeros((16,16), dtype=np.uint8)  # row output, col input
    for j in range(16):
        st = [0]*16
        st[j] = 1
        y = L(st)
        M[:,j] = y
    return M


LMAT = L_matrix()


def exact_two_round_q(N: np.ndarray, linear_coeff: int, gamma: int) -> np.ndarray:
    """Integer numerators q^2 Q(a) for a fixed second-S output byte event.

    w_b = DDT[linear_coeff*b, gamma].  Then q^2 Q = N w.
    The returned vector has denominator 65536.
    """
    w = DDT[MP[linear_coeff].astype(int), gamma].astype(np.int64)
    return N.astype(np.int64) @ w


def all_l_coefficients() -> list[int]:
    return sorted(set(int(x) for x in LMAT.flat))


def find_best_q_event(c: int, allowed_rows: list[int] | None = None) -> dict:
    N = inner_table(c)
    best = (-1, None)
    for coef in all_l_coefficients():
        T = DDT[MP[coef].astype(int),:].astype(np.int64)  # b x gamma
        Qnum = N.astype(np.int64) @ T
        for gamma in range(1,256):
            if allowed_rows is None:
                guarantee = int(Qnum[:,gamma].max())
            else:
                guarantee = min(int(Qnum[a,gamma]) for a in allowed_rows)
            if guarantee > best[0]:
                best = (guarantee,(coef,gamma,Qnum[:,gamma].copy()))
    guarantee,(coef,gamma,profile) = best
    j,i = next((j,i) for j in range(16) for i in range(16) if int(LMAT[i,j]) == coef)
    return {"guarantee_num": guarantee, "coef": coef, "gamma": gamma,
            "input_byte": j, "output_byte": i, "profile_num": profile}


def weak_key_bytes(c: int, rows: list[int], external_a: int = 0) -> list[int]:
    inv = gf_inv(1 ^ c, MP)
    return [int(MP[inv, external_a ^ a]) for a in rows]


def random_permutation_nonzero_byte_baseline(t_active_bytes: int = 1) -> Fraction:
    """Ensemble probability for a fixed nonzero projected output byte.

    A has 2^(128-8t) fixed points when t byte multipliers are nontrivial and
    the inactive external offsets are zero.
    """
    N = 1 << 128
    F = 1 << (128 - 8*t_active_bytes)
    M = 256
    return Fraction(N-F,N) * Fraction(N//M,N-1)


def multiplier_spectrum(outdir: Path) -> tuple[np.ndarray,np.ndarray,np.ndarray]:
    hidden = [np.zeros(256,dtype=np.uint16)] + [hidden_hist(l) for l in range(1,256)]
    hidden = np.stack(hidden)
    hmax = hidden.max(axis=1)
    delta = np.zeros(256,dtype=int)
    energy = np.zeros(256,dtype=np.int64)
    rows = []
    for c in range(1,256):
        N = inner_table(c)
        m = inner_metrics(N)
        delta[c] = m['delta_full']
        energy[c] = m['energy']
        invc = gf_inv(c,MP)
        rows.append({"c":f"0x{c:02x}","inverse":f"0x{invc:02x}",**m})
    # Transfer score B(c): best ceil(H_lambda(b)/2^rank)
    B = np.zeros(256,dtype=int)
    for c in range(1,256):
        best = (0,None)
        for lam in range(1,256):
            r = disagreement_rank(c,lam)
            h = int(hmax[lam])
            v = (h + (1<<r)-1)//(1<<r)
            if v > best[0]:
                best = (v,(lam,r,h,int(np.argmax(hidden[lam]))))
        B[c] = best[0]
        row = rows[c-1]
        lam,r,h,b = best[1]
        row.update({"transfer_bound_B":int(B[c]),"best_hidden_lambda":f"0x{lam:02x}",
                    "disagreement_rank":r,"hidden_peak_h":h,"hidden_peak_b":f"0x{b:02x}"})
    with (outdir/'multiplier_spectrum.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0].keys()));w.writeheader();w.writerows(rows)
    idx=np.arange(2,256)
    corr=float(np.corrcoef(B[idx],delta[idx])[0,1])
    return delta,energy,B,corr


def perrin_cases(outdir: Path) -> list[dict]:
    cases=[(0x02,0x12),(0x04,0x26),(0x10,0x24),(0x1d,0x30),(0x03,0xa2)]
    out=[]
    for lam,b in cases:
        H=hidden_hist(lam); h=int(H[b]); r=disagreement_rank(lam,lam)
        fibers=transfer_fibers(lam,lam,b)
        N=inner_table(lam)
        colE=int(np.sum(N[:,b].astype(np.int64)**2))
        fiberE=sum(v*v for v in fibers.values())
        out.append({
            "c_public":f"0x{lam:02x}","lambda_hidden":f"0x{lam:02x}","b":f"0x{b:02x}",
            "hidden_count_h":h,"rank_r":r,"cell_lower_bound_ceil_h_over_2r":math.ceil(h/(1<<r)),
            "energy_lower_h2_over_2r":h*h/(1<<r),
            "sharp_integer_energy_lower":sharp_integer_energy_lower(h,r),
            "exact_fiber_energy":fiberE,"exact_public_column_energy":colE,
            "fibers":";".join(f"0x{a:02x}:{v}" for a,v in sorted(fibers.items(),key=lambda z:(-z[1],z[0])))
        })
    with (outdir/'perrin_transfer.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(out[0].keys()));w.writeheader();w.writerows(out)
    return out


def two_round_outputs(outdir: Path) -> dict:
    # Strong Perrin rows for c=02.
    N2=inner_table(0x02)
    event=find_best_q_event(0x02, allowed_rows=[0x00,0xde])
    prof=event['profile_num']
    gamma=event['gamma']; coef=event['coef']
    # Full profile with whitening-byte map for external a=0.
    keys=weak_key_bytes(0x02,list(range(256)),0)
    profile_rows=[]
    for a in range(256):
        profile_rows.append({"effective_row_a":f"0x{a:02x}","whitening_key_byte":f"0x{keys[a]:02x}",
                             "q_numerator":int(prof[a]),"q_probability":int(prof[a])/65536.0,
                             "ratio_to_1_over_256":int(prof[a])/256.0})
    with (outdir/'two_round_q_profile_c02.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(profile_rows[0].keys()));w.writeheader();w.writerows(profile_rows)

    # Optimal density/probability frontier, varying the output event for each desired weak-key set size.
    sizes=[1,2,4,8,16,32,64,128]
    coeffs=all_l_coefficients()
    best_by_size={s:(-1,None) for s in sizes}
    for coef0 in coeffs:
        T=DDT[MP[coef0].astype(int),:].astype(np.int64)
        Qnum=N2.astype(np.int64)@T
        for gam in range(1,256):
            vals=Qnum[:,gam]
            order=np.argsort(vals)[::-1]
            for s in sizes:
                guarantee=int(vals[order[s-1]])
                if guarantee>best_by_size[s][0]:
                    best_by_size[s]=(guarantee,(coef0,gam,order[:s].copy(),vals.copy()))
    frontier=[]
    for s in sizes:
        val,(coef0,gam,inds,vals)=best_by_size[s]
        j,i=next((j,i) for j in range(16) for i in range(16) if int(LMAT[i,j])==coef0)
        inds=[int(x) for x in inds]
        wk=weak_key_bytes(0x02,inds,0)
        frontier.append({"weak_key_byte_values":s,"master_key_density":s/256.0,
                         "master_key_count":f"{s}*2^248", "guaranteed_q_num":val,
                         "guaranteed_probability":val/65536.0,"ratio_to_1_over_256":val/256.0,
                         "input_byte_j":j,"output_byte_i":i,"L_coefficient":f"0x{coef0:02x}",
                         "gamma":f"0x{gam:02x}","effective_rows":";".join(f"0x{x:02x}" for x in inds),
                         "key_bytes":";".join(f"0x{x:02x}" for x in wk)})
    with (outdir/'two_round_weakkey_tradeoff.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(frontier[0].keys()));w.writeheader();w.writerows(frontier)

    # Classical best within identical one-active-input / one-byte-output family.
    classical=find_best_q_event(0x01, allowed_rows=None)
    # exclude a=0 classical row: search explicitly
    best_class=(-1,None)
    N1=inner_table(1)
    for coef0 in coeffs:
        T=DDT[MP[coef0].astype(int),:].astype(np.int64)
        Qnum=N1.astype(np.int64)@T
        sub=Qnum[1:,1:]
        idx=np.unravel_index(int(np.argmax(sub)),sub.shape)
        val=int(sub[idx]); a=idx[0]+1; gam=idx[1]+1
        if val>best_class[0]:best_class=(val,(coef0,a,gam))
    cval,(ccoef,ca,cgam)=best_class
    cj,ci=next((j,i) for j in range(16) for i in range(16) if int(LMAT[i,j])==ccoef)

    # Variance/energy connection for the c=02 two-row event.
    wvec=DDT[MP[coef].astype(int),gamma].astype(float)
    qprob=prof.astype(float)/65536.0
    m2=inner_metrics(N2)
    variance=float(np.mean((qprob-1/256.0)**2))
    wt_norm=float(np.sum((wvec-1.0)**2))
    variance_bound=(m2['energy']-65536)*wt_norm/(256**5)

    p0=random_permutation_nonzero_byte_baseline(1)
    summary={
        "c02_event": {"j":event['input_byte'],"i":event['output_byte'],"coef":f"0x{coef:02x}",
                      "gamma":f"0x{gamma:02x}","row00_num":int(prof[0]),"rowde_num":int(prof[0xde]),
                      "row00_key":"0x00","rowde_key":"0x4a",
                      "weak_union_density":2/256,"weak_union_master_keys":"2^249",
                      "guaranteed_probability":min(int(prof[0]),int(prof[0xde]))/65536.0},
        "classical_same_family_best":{"num":cval,"probability":cval/65536.0,"j":cj,"i":ci,
                                      "coef":f"0x{ccoef:02x}","input_difference":f"0x{ca:02x}",
                                      "gamma":f"0x{cgam:02x}"},
        "random_permutation_nonzero_byte_baseline":{"numerator":str(p0.numerator),"denominator":str(p0.denominator),
                                                     "float":float(p0)},
        "q_profile_mean":float(qprob.mean()),"q_profile_variance":variance,
        "energy_variance_upper_bound":variance_bound,"energy":m2['energy'],
        "continuation_centered_norm2":wt_norm,
    }
    return summary


def monte_carlo_two_round(samples: int, seed: int=7) -> dict:
    """Validate the c=02, j=4 -> i=6, gamma=9c event for two weak key bytes."""
    rng=np.random.default_rng(seed)
    def L_batch(A: np.ndarray) -> np.ndarray:
        out=np.zeros_like(A)
        for i in range(16):
            z=np.zeros(A.shape[0],dtype=np.uint8)
            for j in range(16):
                z ^= MP[int(LMAT[i,j]),A[:,j]]
            out[:,i]=z
        return out
    results={}
    for keybyte,theory in [(0x00,794/65536),(0x4a,768/65536)]:
        x=rng.integers(0,256,size=(samples,16),dtype=np.uint8)
        xp=x.copy(); xp[:,4]=MP[0x02,x[:,4]]
        K1=rng.integers(0,256,size=16,dtype=np.uint8);K1[4]=keybyte
        K2=rng.integers(0,256,size=16,dtype=np.uint8)
        z=L_batch(SBOX[x ^ K1]); zp=L_batch(SBOX[xp ^ K1])
        s2=SBOX[z ^ K2]; s2p=SBOX[zp ^ K2]
        obs=float(np.mean((s2 ^ s2p)[:,6] == 0x9c))
        results[f"0x{keybyte:02x}"]={"observed":obs,"theory":theory,"samples":samples}
    return results


def optional_power_table(outdir: Path, p1: float, p0: float) -> None:
    try:
        from scipy.stats import binom
    except Exception:
        return
    goals=[(0.05,0.80),(0.01,0.90),(0.001,0.90)]
    rows=[]
    for alpha,power in goals:
        found=None
        for n in range(10,10000):
            k=int(binom.isf(alpha,n,p0)+1)
            while k>0 and binom.sf(k-2,n,p0)<=alpha:k-=1
            while binom.sf(k-1,n,p0)>alpha:k+=1
            pw=float(binom.sf(k-1,n,p1))
            if pw>=power:
                found=(n,k,float(binom.sf(k-1,n,p0)),pw);break
        if found:
            n,k,a,pw=found
            rows.append({"alpha_target":alpha,"power_target":power,"pairs":n,"accept_count_at_least":k,
                         "actual_alpha":a,"actual_power":pw})
    if rows:
        with (outdir/'two_round_fixed_event_power.csv').open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=list(rows[0].keys()));w.writeheader();w.writerows(rows)



# ------------------------- v2 exact key-recovery layer -------------------------

def full_column_energy_output(outdir: Path) -> None:
    """Write E_{c,b}=sum_a N_c(a,b)^2 for every nonzero c and every b."""
    path = outdir / 'column_energy_Ecb.csv'
    with path.open('w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['c','b','E_cb'])
        for c in range(1,256):
            N = inner_table(c).astype(np.int64)
            Ecb = np.sum(N*N, axis=0)
            for b in range(256):
                w.writerow([f'0x{c:02x}', f'0x{b:02x}', int(Ecb[b])])


def hidden_peak_and_rank_outputs(outdir: Path) -> None:
    """Write the hidden multiplicative peak spectrum and the complete disagreement-rank matrix."""
    with (outdir/'hidden_peak_spectrum.csv').open('w', newline='') as f:
        w = csv.writer(f); w.writerow(['lambda','hidden_peak_h','hidden_peak_b'])
        for lam in range(1,256):
            H = hidden_hist(lam)
            b = int(np.argmax(H))
            w.writerow([f'0x{lam:02x}', int(H[b]), f'0x{b:02x}'])
    R = np.zeros((255,255), dtype=np.uint8)
    for ci,c in enumerate(range(1,256)):
        for li,lam in enumerate(range(1,256)):
            R[ci,li] = disagreement_rank(c,lam)
    np.save(outdir/'disagreement_rank_matrix_uint8.npy', R)


def theorem_audit() -> dict:
    """Independent algebraic invariants used as fail-fast regression checks."""
    assert len(set(map(int,SBOX))) == 256
    assert np.all(DDT.sum(axis=1) == 256)
    assert int(DDT[1:].max()) == 8
    # Degree-rank bound for the same byte representative in the two fields.
    max_slack = 0
    for c in range(1,256):
        r = disagreement_rank(c,c)
        deg = c.bit_length()-1
        assert r <= deg, (c,r,deg)
        max_slack = max(max_slack, deg-r)
    # Selected complete-table stochasticity and inverse-pair identities.
    for c in [0x02,0xe1,0x04,0x91,0x03,0xbe,0x10,0x1d]:
        N = inner_table(c)
        assert np.all(N.sum(axis=1) == 256)
        assert np.all(N.sum(axis=0) == 256)
        ci = gf_inv(c,MP)
        Ni = inner_table(ci)
        for a in range(256):
            assert np.array_equal(N[a], Ni[int(MP[ci,a])])
    # Energy identity and conservation over all nonzero multipliers.
    energies=[]
    for c in range(1,256):
        N=inner_table(c).astype(np.int64)
        E=int(np.sum(N*N)); energies.append(E)
        rhs=0
        for a in range(256):
            rhs += int(np.dot(DDT[a].astype(np.int64), DDT[int(MP[c,a])].astype(np.int64)))
        assert E == rhs, (c,E,rhs)
    expected = 2*(Q-1)*(Q**2)
    assert sum(energies) == expected, (sum(energies),expected)
    return {'sbox_permutation':True,'ddt_row_sum':256,'classical_du_nonzero':8,
            'degree_rank_bound_all_c':True,'max_degree_rank_slack':max_slack,
            'selected_inner_double_stochasticity':True,'selected_inverse_symmetry':True,
            'energy_row_correlation_all_c':True,'energy_conservation_sum':expected}


def round_constant(i: int) -> list[int]:
    return L([0]*15 + [i])


def xor_state(a, b):
    return [int(x)^int(y) for x,y in zip(a,b)]


def standard_round_keys(master_key: bytes) -> list[np.ndarray]:
    """RFC-7801 Kuznyechik round keys K1..K10; master_key is 32 bytes."""
    if len(master_key) != 32:
        raise ValueError('master key must be 32 bytes')
    a=list(master_key[:16]); b=list(master_key[16:]); out=[a.copy(),b.copy()]
    for j in range(1,33):
        t = xor_state(a, round_constant(j))
        t = L([int(SBOX[x]) for x in t])
        a,b = xor_state(t,b), a
        if j % 8 == 0:
            out += [a.copy(),b.copy()]
    return [np.array(x,dtype=np.uint8) for x in out]


def linear_matrix_of(func) -> np.ndarray:
    M=np.zeros((16,16),dtype=np.uint8)
    for j in range(16):
        x=[0]*16; x[j]=1
        M[:,j]=func(x)
    return M


LINV_MAT = linear_matrix_of(L_inv)


def linear_batch(A: np.ndarray, M: np.ndarray) -> np.ndarray:
    out=np.zeros_like(A)
    for i in range(16):
        z=np.zeros(A.shape[0],dtype=np.uint8)
        for j in range(16):
            z ^= MP[int(M[i,j]), A[:,j]]
        out[:,i]=z
    return out


def encrypt_standard_2r_batch(P: np.ndarray, keys: list[np.ndarray]) -> np.ndarray:
    """Two reduced rounds of standard Kuznyechik: K1 whitening, then K2 and K3."""
    X = P ^ keys[0]
    X = linear_batch(SBOX[X], LMAT) ^ keys[1]
    X = linear_batch(SBOX[X], LMAT) ^ keys[2]
    return X


def q_channel(c: int, coef: int) -> np.ndarray:
    """P[alpha,gamma] for the exact two-round observed-byte channel."""
    N=inner_table(c).astype(np.float64)
    T=DDT[MP[coef].astype(int),:].astype(np.float64)
    P=(N @ T)/65536.0
    # Exact integer row sums imply this up to floating conversion.
    assert np.allclose(P.sum(axis=1),1.0)
    return P


def bhattacharyya_worst(P: np.ndarray) -> tuple[float,float,tuple[int,int]]:
    S=np.sqrt(P)
    BC=S@S.T
    np.fill_diagonal(BC,-1.0)
    flat=int(np.argmax(BC)); pair=np.unravel_index(flat,BC.shape)
    rho=float(BC.flat[flat]); D=-math.log(rho)
    return rho,D,(int(pair[0]),int(pair[1]))


def per_byte_recovery_design(c: int, total_error: float=0.01) -> dict:
    """Choose, for each active input byte j, the output byte i with best worst-key separation."""
    cache={}; rows=[]
    for j in range(16):
        cand=[]
        for i in range(16):
            coef=int(LMAT[i,j])
            if coef not in cache:
                P=q_channel(c,coef); rho,D,pair=bhattacharyya_worst(P)
                nz=P[P>0]
                MI=float(np.sum(nz*np.log2(256.0*nz))/256.0)
                cache[coef]=(P,rho,D,pair,MI)
            P,rho,D,pair,MI=cache[coef]
            cand.append((D,i,coef,rho,pair,MI))
        D,i,coef,rho,pair,MI=max(cand,key=lambda z:z[0])
        rows.append({'j':j,'i':i,'coef':coef,'rho':rho,'Dmin':D,
                     'hard_row_1':pair[0],'hard_row_2':pair[1],'uniform_key_MI_bits_per_pair':MI})
    worst_D=min(r['Dmin'] for r in rows)
    # Pairwise MLE error <= 255*rho^N. Union over 16 bytes gives <= total_error.
    N_all=math.ceil(math.log(255*16/total_error)/worst_D)
    N_byte=math.ceil(math.log(255/total_error)/worst_D)
    return {'c':c,'rows':rows,'worst_Dmin':worst_D,'pairs_per_byte_all16_bound':N_all,
            'pairs_worst_byte_1pct_bound':N_byte,'total_error_target':total_error,
            'chosen_plaintext_pairs':16*N_all,'chosen_plaintext_queries_with_reused_base':17*N_all}


def write_recovery_design(outdir: Path, c: int, total_error: float=0.01) -> dict:
    d=per_byte_recovery_design(c,total_error)
    with (outdir/f'whitening_key_recovery_design_c{c:02x}.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(d['rows'][0].keys())); w.writeheader(); w.writerows(d['rows'])
    return d


def recover_whitening_key_demo(c: int, samples: int, seed: int=20260904) -> dict:
    """Cipher-level demonstration using the RFC test master key and only ciphertext differences."""
    master=bytes.fromhex('8899aabbccddeeff0011223344556677fedcba98765432100123456789abcdef')
    keys=standard_round_keys(master)
    expected=[
        '8899aabbccddeeff0011223344556677','fedcba98765432100123456789abcdef',
        'db31485315694343228d6aef8cc78c44','3d4553d8e9cfec6815ebadc40a9ffd04',
        '57646468c44a5e28d3e59246f429f1ac','bd079435165c6432b532e82834da581b',
        '51e640757e8745de705727265a0098b1','5a7925017b9fdd3ed72a91a22286f984',
        'bb44e25378c73123a5f32f73cdb6e517','72e9dd7416bcf45b755dbaa88e4a4043']
    assert [bytes(x).hex() for x in keys] == expected
    design=per_byte_recovery_design(c,0.01)
    rng=np.random.default_rng(seed)
    base=rng.integers(0,256,size=(samples,16),dtype=np.uint8)
    C0=encrypt_standard_2r_batch(base,keys)
    recovered=[]; details=[]
    for r in design['rows']:
        j=r['j']; i=r['i']; coef=r['coef']; Pdist=q_channel(c,coef)
        xp=base.copy(); xp[:,j]=MP[c,xp[:,j]]
        Cj=encrypt_standard_2r_batch(xp,keys)
        # final key cancels; L^{-1} of ciphertext XOR exposes Delta S_2.
        obs=linear_batch(C0 ^ Cj, LINV_MAT)[:,i]
        counts=np.bincount(obs,minlength=256).astype(np.float64)
        logP=np.where(Pdist>0,np.log(Pdist),-np.inf)
        scores=np.full(256,-np.inf)
        for kb in range(256):
            alpha=int(MP[1^c,kb])  # a=0, alpha=(1+c)K0,j
            lp=logP[alpha]
            if not np.any(np.isneginf(lp)&(counts>0)):
                scores[kb]=float(np.dot(counts,np.where(np.isfinite(lp),lp,0.0)))
        order=np.argsort(scores)[::-1]
        rec=int(order[0]); recovered.append(rec)
        details.append({'j':j,'true':int(keys[0][j]),'recovered':rec,'runner_up':int(order[1]),
                        'loglikelihood_margin':float(scores[rec]-scores[int(order[1])]),
                        'i':i,'coef':coef})
    ok=bytes(recovered)==bytes(keys[0])
    return {'c':f'0x{c:02x}','samples_per_byte':samples,'base_seed':seed,
            'true_whitening_key':bytes(keys[0]).hex(),'recovered_whitening_key':bytes(recovered).hex(),
            'success':ok,'chosen_plaintext_queries_with_reused_base':17*samples,
            'chosen_plaintext_pairs':16*samples,'details':details}


def full_c_recovery_search(outdir: Path, total_error: float=0.01) -> None:
    """Slow (~45 s): rank all nonclassical c by the rigorous all-16-byte recovery bound."""
    rows=[]
    for c in range(2,256):
        d=per_byte_recovery_design(c,total_error)
        worst=min(d['rows'],key=lambda r:r['Dmin'])
        rows.append({'c':f'0x{c:02x}','worst_Dmin_across_bytes':d['worst_Dmin'],
                     'N_all16_1pct':d['pairs_per_byte_all16_bound'],
                     'chosen_queries_17N':d['chosen_plaintext_queries_with_reused_base'],
                     'worst_j':worst['j'],'selected_i':worst['i'],'coef':f"0x{worst['coef']:02x}"})
    rows.sort(key=lambda r:r['N_all16_1pct'])
    with (outdir/'all_c_full_whitening_key_search_recomputed.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0].keys()));w.writeheader();w.writerows(rows)

def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',default='results',help='output directory')
    ap.add_argument('--mc',type=int,default=0,help='optional Monte-Carlo samples for the c=02 fixed-event check')
    ap.add_argument('--key-demo',type=int,default=0,help='run RFC-key two-round whitening-key recovery with this many samples per byte')
    ap.add_argument('--key-c',type=lambda x:int(x,0),default=0x04,help='multiplier for whitening-key recovery (default 0x04)')
    ap.add_argument('--full-c-key-search',action='store_true',help='slow: recompute the all-c key-recovery ranking')
    ap.add_argument('--extended-outputs',action='store_true',help='write full E_{c,b}, hidden peaks, and rank matrix')
    args=ap.parse_args()
    outdir=Path(args.out);outdir.mkdir(parents=True,exist_ok=True)
    rfc_regression_tests()
    audit=theorem_audit()
    delta,energy,B,corr=multiplier_spectrum(outdir)
    pcases=perrin_cases(outdir)
    two=two_round_outputs(outdir)
    p0=two['random_permutation_nonzero_byte_baseline']['float']
    optional_power_table(outdir,two['c02_event']['guaranteed_probability'],p0)
    recovery_c02=write_recovery_design(outdir,0x02,0.01)
    recovery_c04=write_recovery_design(outdir,0x04,0.01)
    if args.extended_outputs:
        full_column_energy_output(outdir)
        hidden_peak_and_rank_outputs(outdir)
    if args.full_c_key_search:
        full_c_recovery_search(outdir,0.01)
    result={'rfc_tests':'PASS','theorem_audit':audit,'transfer_B_vs_delta_pearson_nonclassical':corr,
            'selected_metrics':{},'perrin_cases':pcases,'two_round':two,
            'whitening_key_recovery_c02':{k:v for k,v in recovery_c02.items() if k!='rows'},
            'whitening_key_recovery_c04':{k:v for k,v in recovery_c04.items() if k!='rows'}}
    for c in [0x02,0xe1,0x04,0x91,0x03,0xbe,0x10,0x1d]:
        result['selected_metrics'][f'0x{c:02x}']=inner_metrics(inner_table(c))
    if args.mc:
        result['monte_carlo']=monte_carlo_two_round(args.mc)
    if args.key_demo:
        result['key_recovery_demo']=recover_whitening_key_demo(args.key_c,args.key_demo)
    (outdir/'summary_v2.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
