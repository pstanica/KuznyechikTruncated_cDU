#!/usr/bin/env python3
"""Two-round standard-Kuznyechik full master-key recovery add-on.

Stage 1 uses the exact Q2 whitening-byte channel from kuz_innerc_repro_v2.py
and recovers K1 (the first 128-bit master-key half / initial whitening key).
Stage 2, after K1 is known, uses chosen internal first-round outputs to place the
same inner-c relation immediately before the second S-box layer and recovers K2,
the second 128-bit master-key half, from the exact inner-table row channel.

All probability bounds are fixed-key and exact for the stated two-round reduced
standard Kuznyechik model.  This is not a full-round attack.
"""
from __future__ import annotations
import argparse, json, math
from pathlib import Path
import numpy as np
import kuz_innerc_repro_v2 as k

SINV=np.empty(256,dtype=np.uint8)
for x,y in enumerate(k.SBOX):
    SINV[int(y)] = x


def bc_separation(P: np.ndarray):
    S=np.sqrt(P)
    BC=S@S.T
    np.fill_diagonal(BC,-1.0)
    flat=int(np.argmax(BC)); pair=np.unravel_index(flat,BC.shape)
    rho=float(BC.flat[flat])
    return rho,-math.log(rho),(int(pair[0]),int(pair[1]))


def second_half_design(c: int, total_error: float=0.005) -> dict:
    """Exact row-channel design for K2 after K1 is known.

    Candidate key bytes k2 map bijectively to alpha=(1+c)k2.  Observing
    L^{-1}(C xor C') at the attacked byte yields one sample from
    N_c(alpha,b)/256.  The union-bound MLE failure is <=16*255*rho^N.
    """
    Ntab=k.inner_table(c).astype(np.float64)
    unique_rows=int(np.unique(Ntab.astype(np.uint16),axis=0).shape[0])
    P=Ntab/256.0
    assert np.allclose(P.sum(axis=1),1.0)
    rho,D,pair=bc_separation(P)
    samples=math.ceil(math.log(16*255/total_error)/D)
    return {
        'c':c,'unique_inner_rows':unique_rows,'rho':rho,'Dmin':D,
        'hard_row_1':pair[0],'hard_row_2':pair[1],
        'total_error_target':total_error,'samples_per_byte_all16_bound':samples,
        'chosen_plaintext_pairs':16*samples,
        'chosen_plaintext_queries_with_reused_base':17*samples,
    }


def plaintexts_for_internal_V(V: np.ndarray, K1: np.ndarray) -> np.ndarray:
    """Invert V=L(S(P xor K1)) for arbitrary selected V states."""
    return SINV[k.linear_batch(V,k.LINV_MAT)] ^ K1


def recover_second_half(c: int, samples: int, K1: np.ndarray, keys: list[np.ndarray], seed: int=20260905) -> dict:
    """Recover K2 from a two-round encryption oracle, assuming K1 is known."""
    rng=np.random.default_rng(seed)
    V=rng.integers(0,256,size=(samples,16),dtype=np.uint8)
    P0=plaintexts_for_internal_V(V,K1)
    C0=k.encrypt_standard_2r_batch(P0,keys)
    Prows=k.inner_table(c).astype(np.float64)/256.0
    with np.errstate(divide='ignore'):
        logP=np.where(Prows>0,np.log(Prows),-np.inf)
    recovered=[]; details=[]
    for j in range(16):
        Vp=V.copy(); Vp[:,j]=k.MP[c,V[:,j]]  # external offset a=0
        Pp=plaintexts_for_internal_V(Vp,K1)
        Cp=k.encrypt_standard_2r_batch(Pp,keys)
        # Final K3 cancels; L^{-1} exposes S2-output difference exactly.
        obs=k.linear_batch(C0 ^ Cp,k.LINV_MAT)[:,j]
        counts=np.bincount(obs,minlength=256).astype(np.float64)
        scores=np.full(256,-np.inf)
        for kb in range(256):
            alpha=int(k.MP[1^c,kb])
            lp=logP[alpha]
            impossible=np.isneginf(lp) & (counts>0)
            if not np.any(impossible):
                scores[kb]=float(np.dot(counts,np.where(np.isfinite(lp),lp,0.0)))
        order=np.argsort(scores)[::-1]
        rec=int(order[0]); recovered.append(rec)
        finite_alts=[int(x) for x in order[1:] if np.isfinite(scores[int(x)])]
        if finite_alts:
            runner=finite_alts[0]
            margin=float(scores[rec]-scores[runner])
            status='finite likelihood margin'
        else:
            runner=None
            margin=None
            status='all 255 alternative candidates excluded by observed support'
        details.append({'j':j,'true':int(keys[1][j]),'recovered':rec,'runner_up':runner,
                        'loglikelihood_margin':margin,'decision_status':status})
    return {
        'c':f'0x{c:02x}','samples_per_byte':samples,
        'true_second_master_half':bytes(keys[1]).hex(),
        'recovered_second_master_half':bytes(recovered).hex(),
        'success':bytes(recovered)==bytes(keys[1]),
        'chosen_plaintext_pairs':16*samples,
        'chosen_plaintext_queries_with_reused_base':17*samples,
        'details':details,
    }


def end_to_end_demo(c: int=0x04, total_error: float=0.01, seed1: int=20260904, seed2: int=20260905) -> dict:
    """Recover both 128-bit master-key halves for two-round standard Kuznyechik."""
    # Allocate half of the rigorous error budget to each stage.
    eps1=total_error/2.0; eps2=total_error/2.0
    d1=k.per_byte_recovery_design(c,eps1)
    d2=second_half_design(c,eps2)
    n1=d1['pairs_per_byte_all16_bound']; n2=d2['samples_per_byte_all16_bound']

    master=bytes.fromhex('8899aabbccddeeff0011223344556677fedcba98765432100123456789abcdef')
    keys=k.standard_round_keys(master)
    stage1=k.recover_whitening_key_demo(c,n1,seed1)
    K1rec=np.frombuffer(bytes.fromhex(stage1['recovered_whitening_key']),dtype=np.uint8).copy()
    stage2=recover_second_half(c,n2,K1rec,keys,seed2)
    recovered=bytes.fromhex(stage1['recovered_whitening_key']+stage2['recovered_second_master_half'])
    return {
        'model':'two-round standard Kuznyechik with initial whitening and RFC key schedule',
        'c':f'0x{c:02x}','total_failure_bound_target':total_error,
        'stage1_failure_budget':eps1,'stage2_failure_budget':eps2,
        'stage1_samples_per_byte':n1,'stage2_samples_per_byte':n2,
        'stage1':stage1,'stage2':stage2,
        'true_master_key':master.hex(),'recovered_master_key':recovered.hex(),
        'success':recovered==master,
        'total_chosen_plaintext_pairs':16*(n1+n2),
        'total_chosen_plaintext_queries':17*(n1+n2),
        'rigorous_union_bound_note':'stage1 failure <= eps1 and stage2 failure <= eps2; hence total failure <= eps1+eps2',
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--c',type=lambda x:int(x,0),default=0x04)
    ap.add_argument('--error',type=float,default=0.01)
    ap.add_argument('--out',default='results_v3.json')
    args=ap.parse_args()
    k.rfc_regression_tests()
    audit=k.theorem_audit()
    d2=second_half_design(args.c,args.error/2)
    res=end_to_end_demo(args.c,args.error)
    res['base_theorem_audit']=audit
    res['second_half_design']=d2
    Path(args.out).write_text(json.dumps(res,indent=2,allow_nan=False))
    print(json.dumps(res,indent=2,allow_nan=False))

if __name__=='__main__':
    main()
