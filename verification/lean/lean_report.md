# Lean 4 verification report

**Manuscript:** *A Lifting Criterion for Subalgebra Bases beyond Term Orders and Integral Domains* (A. Abbas, J. A. Khan)
**File:** `SSOrder.lean` (317 lines)
**Toolchain:** Lean 4.15.0 (x86_64 Linux), core library only — **no Mathlib**
**Date:** 17 October 2026

> Inherited unchanged from the referee's verification package. Only this report was updated: references now use the numbering of the **revised** manuscript. The Lean names `ex24_*` refer to the submitted numbering (Example 2.4, now Example 2.5).

## Result

`lean SSOrder.lean` completes with no errors and no warnings. The file contains no `sorry`. The output of `#print axioms` (file `out_axioms.txt`) shows every theorem depends either on no axioms or only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Lean name | Axioms |
|---|---|
| `SS.add_right_cancel` | none |
| `SS.lsum_lt_or_eq` | none |
| `SS.lsum_le_of_forall2` | none |
| `SS.not_lt_zero` | none |
| `SS.zero_le` | none |
| `SS.fdeg_lt` | propext, Classical.choice, Quot.sound |
| `SS.no_infinite_descent` | none |
| `SS.exists_minimal` | propext, Classical.choice, Quot.sound |
| `SS.descent_reaches` | propext, Classical.choice, Quot.sound |
| `Examples.lex_wf` | none |
| `Examples.ex24_degree_drop` | propext, Quot.sound |
| `Examples.ex24_degrees` | propext, Quot.sound |
| `Examples.ex46_formal_vs_actual` | none |

## What is formalized

| Statement | Role in the manuscript / report |
|---|---|
| Class `SS.OrdMonoid`: commutative monoid, strict total order, `a < b → a + c < b + c` | Standing hypothesis on Γ (Definition 1.1, Remark 1.4) |
| `add_right_cancel`: `a + c = b + c → a = b` | Cancellativity used in Theorem 3.3 (⇐) |
| `lsum_lt_or_eq`, `lsum_le_of_forall2`: if `δₖ ≼ υₖ` for every k, then `∑δₖ ≺ ∑υₖ` unless the lists coincide | Degree bookkeeping in Lemma 2.7(i) |
| `not_lt_zero`, `zero_le`: in a well-ordered compatible monoid, 0 is least | First step of Lemma 3.9 |
| `fdeg_lt`: if every `υ(fᵢ) > 0` and `α ≤ β` componentwise, `α ≠ β`, then `deg_F(α) < deg_F(β)` | Antichain step of Lemma 3.9 |
| `no_infinite_descent` | Lemma 2.10 (termination of s-reduction) |
| `exists_minimal` | Choice of a representation with minimal Ω in Theorem 3.3 (⇐) |
| `descent_reaches` | Descent step of Lemma 3.12 and Theorem 3.13 (termination of Algorithm 1) |
| `OrdMonoid (ℕ × ℕ)` instance with lexicographic order; `lex_wf` | The gradings of Examples 1.6, 2.5, 4.2, 4.6, 4.10 satisfy the hypotheses |
| `ex24_degree_drop`: `(2j+3, 2j+1) < (2j+4, 2j)` | Degree drop in the liftings of Proposition 3.15 (Example 2.5) |
| `ex24_degrees` | Additivity of degrees along `g₁gₙ = g₂gₙ₋₁` |
| `ex46_formal_vs_actual`: `(0,6) < (2,0)` | Example 4.6: formal degree of `Y₃²` exceeds the actual degree of `f₃² = y⁶` |

Core Lean 4 has no `List.Forall₂` without Mathlib or Batteries, so the file defines its own `Forall2`.

## What is not formalized

Graded rings and their homogeneous components; leading forms; the polynomial ring `S[Y]` and its grading by formal degrees; the maps π and ψ; kernels and liftings; Dickson's lemma. Consequently Lemma 2.7 (beyond its order-theoretic core), Lemma 3.1, Theorems 2.13, 3.3 and 3.13, Propositions 3.4, 3.10, 3.15 and 4.13, Lemma 4.1 and Algorithm 1 are **not** formally verified. Their proofs are given in the manuscript and have been checked by hand, not by machine.

## Why Mathlib was not used

Mathlib's prebuilt cache is downloaded from a host that the review environment could not reach, and building Mathlib from source was not practical there. The Lean 4.15.0 toolchain itself was installed directly from its GitHub release.

## Feasibility of a full formalization

With Mathlib, the following infrastructure exists: graded algebras via `DirectSum.Decomposition` / `GradedAlgebra`, homogeneous ideals, `MvPolynomial` with weighted homogeneous components (`MvPolynomial.weightedHomogeneousComponent`), well-founded and partially well-ordered sets (`Set.PartiallyWellOrderedOn`, which yields Dickson-type finiteness). In our estimate, Lemma 2.7, Lemma 3.1, Theorem 2.13 and Theorem 3.3 could be formalized in one to a few thousand lines. The main effort would be grading `S[Y]` by formal degrees with values in an arbitrary well-ordered monoid, and the bookkeeping of homogeneous components of sums of products. This is a worthwhile but separate project and is not a requirement for the paper.

## Reproduce

```
lean SSOrder.lean          # no output = success
./check_axioms.sh          # appends the #print axioms commands and compares with out_axioms.txt
```
