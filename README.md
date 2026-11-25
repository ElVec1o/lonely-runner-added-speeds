# Deleting speeds from {1,...,N} and adding large ones: the bound 1/N, and two deleted speeds larger than N/2

Pre-release draft of 25 November 2026 (private repository). Author: Vico Bonfioli. License: CC-BY-4.0 (`LICENSE.md`). Not peer reviewed. No DOI yet.
Paper: `paper/paperB.pdf` (source `paper/paperB.tex`). Series on Zenodo: A1 (one-entry values) doi:10.5281/zenodo.24531020, A2 (effective Kravitz lemma) doi:10.5281/zenodo.24531022, B (added speeds) doi:10.5281/zenodo.24531025, Lean sources doi:10.5281/zenodo.24531012; dependency diagram `paper/dependency.pdf`.

## Abstract

For a finite set V of positive integers (speeds) let ML(V) = max_t min_{v in V} dist(tv, Z); an N-set is tight if ML = 1/(N+1), the value of [N] = {1,...,N} and the least that the Lonely Runner Conjecture allows. Goddyn and Wong replace entries r_i of [N] by multiples m_i r_i and give a numerical condition on the m_i under which the result stays tight (the acceleration). Zhang's Question 8.1 asks whether every tight set obtained from [N] by replacing two speeds greater than N/2 by two larger speeds arises from this acceleration.
Result (Theorem 1.7, Corollary 1.8): let r_1 < r_2 be coprime speeds in (N/2, N], N >= 4, and w_1 != w_2 integers larger than N; then ([N] minus {r_1, r_2}) u {w_1, w_2} is not tight, which answers Question 8.1 in the coprime case; the case of a common factor, where tight sets exist, is not settled (Conjecture T-X). Also (Theorem 1.1; new only for k >= 2): let r <= N-2 be a deleted speed, k >= 1 and T_k = 3k(k+1)+1; if the interval [N+1+r, 2N-1] contains T_k pairwise coprime integers, each coprime to r, then every set V that omits r, has arbitrary other elements in [1,N] and at most k elements larger than N has ML(V) >= 1/N, strictly above 1/(N+1). The hypothesis holds for every r <= N/2 from an explicit threshold (for example N >= 222 for k = 2); T_k can be replaced by 8k+1 (Theorem 1.4).

## Idea of the proof

A time at which all retained speeds are far from integers is sought among rational times a/D with D in the window [N+1+r, 2N-1] coprime to r. Each added speed can spoil only a bounded total amount of the windows around these times, by a counting argument over the common divisors of the moduli D; with T_k pairwise coprime moduli (or 8k+1 in the linear form) at least one window survives, and a time in it is at distance at least 1/N from an integer for every speed of V. (Informal summary by the packager; the paper's section 3.1 and the paragraph after Theorem 1.1 are authoritative.)

## Main results

Numbers are those of the PDF of this version. "Lean" means: the declarations named are in the Lean repository `lonely-runner-near-tight-lean`, the saved build logs of the author's development tree end with `Build completed successfully`, no `sorryAx` occurs and only the three standard axioms are printed; a clean-checkout build of the umbrella module `LRSpectrumFull.Sext6.Gap.All` (362 modules, public five-speed v1.0.2 plus the overlay) was run on 25 November 2026: 0 failures, and its axiom output is identical to the saved one; the larger `Release` closure was not rebuilt from a clean checkout. The status of every statement of the paper (Lean, hand, computed, conjecture) is the table "Status per statement" in the paper; where the entry below says mixed, that table decides.

| paper | statement (short; the paper has the full statement) | label |
|---|---|---|
| Theorem 1.1 | `k`-rich `(N,r)`, `r` not in `V`, at most `k` elements of `V` above `N`: `ML(V) >= 1/N` | Lean (`Gap.ML_ge_robust`, `theoremS_unconditional`) |
| Theorem 1.2, Corollary 1.3 | thresholds: every `r <= N/2` is `k`-rich for `N >= N*(k)` (`k <= 12`), `N >= max(10^5, 67 T_k^2)`, `N >= M(k)` (`1 <= k <= 30`); rigidity | Lean; the columns for `k >= 31` and the sieve minimality for `k <= 6` are computed |
| Theorem 1.4 | linear count: `8k+1` pairwise coprime moduli suffice (`18k+1` in Stage A) | Lean (`Gap.ML_ge_robust_lin8`, `theoremS_linear`); the value form `2/(D*+1)` is by hand and not claimed |
| Theorem 1.5, Corollary 1.6 | two added speeds, `N >= 222`, `1 <= r <= N/2`: `ML >= 1/N`; several deleted speeds | Theorem 1.5 Lean (`Gap.theoremW_unconditional`); see the status table for Corollary 1.6 |
| Theorem 1.7, Corollary 1.8 | coprime removed speeds `r_1 < r_2` in `(N/2, N]`, any `w_1 != w_2 > N`: not tight (`ML >= 1/N` if each `w_i` is a multiple of one `r_i`) | Lean for `N >= 10` and certificates for `4 <= N <= 9`; Corollary 1.8 by hand |
| Conjecture T-X | for `gcd > 1`: the tight two-entry sets are exactly the known ones | CONJECTURE (computed for `N <= 254`, not claimed) |

Companions: B is readable alone; it quotes the thresholds 14 and 21 of A1 (not used) and A1 uses B Theorem 1.5 for `N >= 222`. The numbers `A1.x.y`, `A2.x.y` in the PDF refer to the companion drafts, which are not released.

## Where the evidence is

* Lean: `Gap/Robust*`, `CopWin*`, `Cheb30*`, `FinalCore`, `LinL*`, `Q81*`, `TwoE*`, `MultiNec*`, `OneOverR`, `Multi*` (rows 8, 12 to 15, 24 to 27, 29 of `repro/MAP.md` in the Lean repository). Saved `#print axioms` lines: `repro/expected_output/` of the Lean repository (names as cited in the paper's Lean section); verdict script `repro/judge_axioms.sh`.
* Computed: `code/` (two-added-speeds engines, coprime-pair certificates, multi-entry scan, prime-window generators and tests, linear-count engines and thresholds). See `code/README.md`: which program supports which statement is the packager's identification, not re-run; a list of computed statements with no identified program is at its end.
* By hand: the arguments of the paper marked "hand"; the ones marked "reviewed" were re-derived by a second pass of an AI system that did not write them. No human referee has read the paper.

## Not done yet

Blind reads by independent readers of the current text, the talk and the FAQ of the release rules, a refresh of the prior-art search (searches of 25 November 2026 are described in the paper and expire), a clean-checkout build of the full `Release` closure of the Lean repository, and a reproduction script for the computed tables.

## Build the paper

`pdflatex` on `paper/paperB.tex`, three rounds (the three drafts read each other's `.aux` files through `xr-hyper`; the companion `.aux` files of this version are in `paper/`; a companion number prints as `??` if they are missing). Compile the companions to regenerate them.

## Files

| path | content |
|---|---|
| `paper/` | `paperB.tex`, `paperB.pdf`, companion `.aux` files, `dependency.tex`, `dependency.pdf` |
| `code/` | the programs cited as "computed" (Rust, C), `build.sh`, `tools/launch_lite.sh`, `README.md` |
| `CHECKSUMS.sha256` | sha256 of every file of this repository except itself; check: `shasum -a 256 -c CHECKSUMS.sha256 | grep -vc ': OK'` prints `0` |
| `CITATION.cff`, `LICENSE.md`, `.gitignore` | citation data, license |

## Use of AI

The mathematical ideas, proofs, computations, Lean code and text of this work were produced with substantial assistance from AI systems (Anthropic's Claude models), working under the direction of the author, V. Bonfioli, who selected the problems, set the standards of verification, reviewed the results and takes responsibility for the contents. Every statement marked Lean-verified is checked by the Lean kernel and the printed axiom lists, not by the author or the AI systems; computed statements come from the programs in the paper repositories; statements labelled by hand are not machine-checked. The arguments marked reviewed were re-derived by a second pass of an AI system that did not write them; no human referee has read them. The arguments have not been refereed.

## Prior art and credit

* Goddyn and Wong (tight instances; the acceleration and the numerical criterion), Kravitz (barely lonely runners; the lemmas on one added speed and Theorem 5.1), Liu (the value of the one-deletion set; survey), Zhang (one-entry modifications and tight instances; Lemma 5.3, Question 8.1), Peng (unrefereed record 24363090), Fan and Sun (amended spectrum conjecture), Jain and Kravitz (relative spectra), Giri and Kravitz (structure of spectra), Yi, Gill and Bu (four runners; the height method), Cordella (six and seven speeds), and the unrefereed repository of 1337isnot1337. Full references and the exact attribution of each result are in the papers (sections "Attribution" and "Prior art").
