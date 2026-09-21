# v3 verified result: two-round standard Kuznyechik

This add-on starts from the exact v2 structural/Q2 computation and pushes the whitening-byte idea one step further.  The result is a **full 256-bit master-key recovery for the two-round reduced standard Kuznyechik model**, not for full 9-round Kuznyechik.

## 1. Stage 1: recover the initial whitening half K1

For one nontrivial plaintext-byte multiplier `c=0x04`, the exact two-round byte channel is

\[
P_k(\gamma)=Q_{c,L[i,j],\gamma}((1\oplus c)k),\qquad
Q_{c,\ell,\gamma}(\alpha)=2^{-16}\sum_b N_c(\alpha,b)D(\ell b,\gamma).
\]

For each plaintext byte `j`, the code selects the output byte `i` maximizing the worst pairwise Bhattacharyya separation.  Across all 16 bytes,

\[
D_{\min}^{(1)}=-\log\rho_1=0.0009642779371385676.
\]

For maximum-likelihood decoding of each of the 256 byte candidates,

\[
\Pr[\widehat K_1\neq K_1]\le 16\cdot255\,\rho_1^{N_1}.
\]

Allocating failure budget `0.005` to this stage gives

\[
N_1=14117
\]

base samples. Reusing each base plaintext across the sixteen one-byte companion experiments costs

- `225872` chosen-plaintext pairs;
- `239989` distinct chosen-plaintext encryption queries.

The RFC master-key test recovers

`K1 = 8899aabbccddeeff0011223344556677`

exactly.

## 2. Stage 2: after K1 is known, recover the second master-key half K2

Once `K1` is recovered, choose an arbitrary internal value

\[
V=L(S(P\oplus K_1)).
\]

Because the first round is invertible, any selected `V` is realized by

\[
P=K_1\oplus S^{-1}(L^{-1}(V)).
\]

For byte `j`, choose a companion `V'` with

\[
V'_j=cV_j,\qquad V'_t=V_t\;(t\ne j).
\]

The inputs to the second S-box layer are `U=V xor K2` and `U'=V' xor K2`, hence at byte `j`

\[
U'_j=cU_j\oplus(1\oplus c)K_{2,j}.
\]

Therefore the observable second-S-box output difference has the **exact** distribution

\[
\Pr[B=b\mid K_{2,j}=k]=\frac{N_c((1\oplus c)k,b)}{256}.
\]

For `c=0x04` all 256 rows of `N_c` are distinct.  The worst pairwise Bhattacharyya coefficient is

\[
\rho_2=0.7074682424211026,
\qquad
D_{\min}^{(2)}=-\log\rho_2=0.34606253750950833.
\]

Thus

\[
\Pr[\widehat K_2\neq K_2]\le 16\cdot255\,\rho_2^{N_2}.
\]

With a stage failure budget `0.005`, only

\[
N_2=40
\]

base samples are required by this rigorous union bound, corresponding to

- `640` chosen-plaintext pairs;
- `680` distinct chosen-plaintext encryption queries.

On the RFC key the program recovers

`K2 = fedcba98765432100123456789abcdef`

exactly.  In the recorded 40-sample run, the observed support already eliminates all 255 incorrect candidates at each byte.  As an implementation regression check, the same stage was also run for 100 independently generated random master keys, with 100/100 successful recoveries.

## 3. End-to-end two-round master-key recovery

Using a total failure target of `0.01`, split equally between the two stages, the rigorous parameters are

\[
N_1=14117,\qquad N_2=40.
\]

Total data/query counts are

- **226512 chosen-plaintext pairs**;
- **240669 distinct chosen-plaintext encryption queries**;
- small offline likelihood work (bytewise 256-candidate scoring).

The end-to-end RFC demonstration recovers the complete 256-bit master key

`8899aabbccddeeff0011223344556677fedcba98765432100123456789abcdef`

exactly.

## 4. Relationship to the 2^-7 Perrin weak-key example

The v2 program already proves that for `c=0x02`, external offset zero and one nontrivial multiplier byte, the Perrin rank-one effective rows `alpha in {00,de}` correspond to whitening-byte values `{00,4a}`.  Hence the weak-key class has density `2/256 = 2^-7`.  A fixed two-round output event has probability at least `3/256` on that class, versus approximately `0.0038909912` under the relevant vector-affine random-permutation baseline.

The v3 recovery result is stronger than this fixed weak-key distinguisher: instead of conditioning on two favorable whitening-byte values, it uses the complete family of 256 exact key-dependent output distributions to decode the unknown whitening byte, and then repeats the inner relation at the second S-box interface after `K1` has been learned.

## 5. Reproducibility and numerical precision

The structural computation and both recovery stages were rerun on the macOS system recorded in `environment.txt`.  The exact checks reproduce the RFC tests, inner-table identities, disagreement ranks, Perrin transfer certificates, energy identities, column energies, determinant certificate, and row-distinctness certificate.  The second recovery stage also succeeds for 100 independently generated master keys.

For the Stage-1 failure budget `0.005` used in the complete two-stage attack, the all-multiplier scan gives `N=13884` for the best inverse class `0x4f/0xaa` and `N=14117` for the structurally selected class `0x04/0x91`.  Thus the selected class requires about `1.68%` more samples than the numerical optimum.  These values are recorded in `outputs/core_results/all_c_stage1_error_0p005.csv`.

The separate file `all_c_full_whitening_key_search_recomputed.csv` uses total error `0.01` for Stage 1 considered alone; its smaller sample counts should not be substituted into the two-stage attack.  Across software versions, floating-point values can differ in their final displayed digits and tied rows can appear in a different order.  These differences do not change any exact certificate, selected multiplier, probability, or reported data complexity.

## 6. Scope limitation

This result is for **two reduced rounds of standard Kuznyechik including initial whitening and the RFC key schedule**.  It does not establish a three-round or full-round key-recovery attack.  Extending the exact `Q_r(alpha)` channel beyond two rounds requires handling the joint post-second-S-box state distribution and additional round-key dependence; that should be treated as the next separate step rather than inferred from the present result.
