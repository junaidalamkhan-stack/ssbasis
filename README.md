# ssbasis.lib 1.1 — subalgebra standard bases (SS-bases) in Singular

Companion code for the paper

> Anum Abbas and Junaid Alam Khan, **A Lifting Criterion for Subalgebra Standard Bases in Monoid-Graded Rings with Zero Divisors**.
> Department of Mathematical Sciences, Institute of Business Administration (IBA), Karachi, Pakistan.

Section 4.1 of the paper describes the library; Lemma 4.1 justifies its two main computational steps. The repository contains the Singular library `ssbasis.lib`, the Singular sessions of the paper with their stored outputs, regression tests, and independent verification scripts in Python and Lean 4.

## Example numbering

The scripts, stored outputs and verification files label the examples as in the revised manuscript that the code was prepared for. The table gives the corresponding numbers in the final version of the paper.

| Label in the code | Final paper | Content |
|---|---|---|
| Example 2.5 | Example 2.5 (see also Example 3.16) | ℚ[x,y,z], ℕ²-grading (a+2b, b+c): no finite SS-basis; natural grading: SS-basis |
| Example 4.6 | Example 4.2 (i) | ℤ₄[x,y], lexicographic multigrading |
| Example 4.7 | Example 4.2 (ii) | ℤ₄[x,y], natural grading: not an SS-basis, one completion step |
| Example 4.9 | Example 4.3 | ℤ₆[x,y], natural grading |
| Example 4.11 | Example 4.4 | dual numbers ℚ[ε]/(ε²), weighted grading |
| Example 4.12 | Example 4.5 | non-reduced algebra K[x,y]/(x²), characteristics 0, 2, 3 |
| Examples 4.2, 4.4, 4.5, 4.10 | — | further sessions over ℤ, ℚ and ℤ₆ kept as additional examples |

Example 1.6 and Remark 2.8 have the same numbers in both versions.

## Installation

Requires [Singular](https://www.singular.uni-kl.de) (tested with 4.3.2). Copy `ssbasis.lib` to your working directory, or to a directory on Singular's library search path (`SINGULARPATH`), and load it with `LIB "ssbasis.lib";`. The verification scripts need only Python 3; the Lean files need Lean 4 (tested with 4.15.0, no Mathlib).

## Quick start

```
LIB "ssbasis.lib";
ring r = (integer,4),(x,y),dp;
ideal G = xy3+y4, y3+2y, 2x+y3;
SSliftingTest(G, ssNatural());          // Example 4.2(ii): NOT an SS-basis
list L = SScomplete(G, ssNatural(), 10);
L[1];                                   // adjoins 2x+2y; L[3] = 1: terminated
```

## Procedures

| Procedure | Purpose |
|---|---|
| `ssNatural()` | 1 × n matrix of ones: the natural grading |
| `ssLex()` | n × n identity: leading forms are leading terms for `lp` (x1 > … > xn) |
| `ssCheckInput(G,W)` | validates the input; raises an `ERROR` with an explanation if unsupported |
| `ssPolyDeg(p,W)`, `ssLeadForm(p,W)` | degree υ(p) and leading form Υ(p) in R (after reduction modulo the quotient ideal) |
| `SSliftingTest(G,W)` | report: degrees and leading forms, homogeneous generators u of ker π with Ω(u), a lifting of each u or, if none exists, a nonzero S-normal form of ψ(u) (the element Algorithm 1 adjoins), and the verdict of Theorem 3.3 |
| `SSliftingData(G,W)` | the same information as a list (for scripts) |
| `SScomplete(G,W,b)` | Algorithm 1 with at most `b` passes; returns `list(F', passes, terminated)` |
| `ssLexCmp`, `ssExpDeg` | helpers, unchanged from version 1.0 |

## Input conventions

* **Coefficients** (`A0`): a field (characteristic 0 or p, also with parameters), `integer` (ℤ) or `(integer,n)` (ℤ/n).
* **Ring**: a polynomial ring `A0[x1..xn]` or a quotient ring (`qring`) by an ideal that is homogeneous for `W`.
* **Grading**: a k × n `intmat` `W` with non-negative entries; the degree of x^a is W·a, compared lexicographically (first row first).
* **Variables of degree 0**: a variable whose column of `W` is zero has degree 0 and belongs to S = R₀. Then S = A0[those variables] modulo the degree-zero part of the quotient ideal. This is how the dual numbers ℚ[ε]/(ε²) are entered (Example 4.4): `ring r = 0,(e,x,y),dp; qring q = std(ideal(e2)); intmat W[1][3] = 0,1,2;`.
* **Generators**: an `ideal G`. Constants (degree 0) are allowed in the lifting test.

## Unsupported input (raises an ERROR)

* negative entries in `W` (Γ would not be well-ordered);
* `W` with no nonzero column, or with the wrong number of columns;
* local or mixed orderings in the basering;
* quotient ideals that are not `W`-homogeneous;
* floating-point coefficients (`real`, `complex`);
* generators that are zero in R;
* ring variables named `Y1`, `Y2`, … (they clash with the auxiliary variables).

## Method (see Section 4.1 and Lemma 4.1 of the paper)

With x₊ the variables of positive degree and x₀ those of degree 0:

1. **Kernels.** ker π and ker ψ come from eliminating x₊ from I + ⟨Yᵢ − Υ(fᵢ)⟩ and I + ⟨Yᵢ − fᵢ⟩ (Remark 3.9). The generators of ker π are split into Ω-homogeneous components and reduced modulo the degree-zero part of I. The elimination for ker ψ uses `eliminate` in a ring with order `dp`, which is much faster than a block-order standard basis for inhomogeneous input.
2. **Lifting test (Lemma 4.1(a)).** u lifts iff its remainder modulo a standard basis of ker ψ, for a global order refining Ω, is 0 or of smaller Ω. The lifting printed is u minus the remainder.
3. **Reduction step (Lemma 4.1(b)).** Υ(g) ∈ S[Υ(F)] iff its remainder modulo a standard basis of I + ⟨Yᵢ − Υ(fᵢ)⟩ for an elimination order involves no variable of x₊. The component of formal degree υ(g) of that remainder gives the reduction step.

Over ℤ and ℤ/n the method relies on Singular's standard bases over these rings being strong standard bases, which is what Lemma 4.1 assumes.

## Known limitations

* Algorithm 1 need not terminate (it terminates iff a finite SS-basis exists, Theorem 3.14), so `SScomplete` takes a bound on the number of passes.
* For inhomogeneous generators over ℤ/n the elimination for ker ψ can be slow. One random test case with three cubic generators over ℤ/4 takes about 9 s, the same as version 1.0.
* Gradings other than ℕᵏ-gradings by weight matrices, and coefficient rings other than fields, ℤ, ℤ/n and their quotients via degree-0 variables, are not implemented. The theory of Sections 2–3 is more general.
* Output polynomials are printed as Singular prints them. Liftings and generating sets are not unique, so they may differ from the tables in the paper; all printed liftings satisfy Definition 3.2 (checked by `verification/check_session_outputs.py`).

## Reproducing the paper

```
./run_tests.sh
```

This runs `examples/examples.sing` (every session in the paper, numbered as in the revised manuscript), `examples/integer_groebner.sing` (the strong Gröbner bases over ℤ used in Example 4.4 to cover every field) and `tests/regression.sing`, compares them with the stored outputs, and runs the independent checks in `verification/`. All outputs were produced with Singular 4.3.2 (build 4330) on Ubuntu 24.04. Another Singular version may print polynomials with terms in a different order or choose different liftings; the independent checks then remain the reference.

## Independent verification (`verification/`)

These scripts use no Singular code; they rely on exact arithmetic in pure Python 3.

| Script | Checks |
|---|---|
| `sslib.py` | exact polynomial arithmetic over ℤ, ℚ, ℤ/n; leading forms; formal degrees; exhaustive liftability test; degree-by-degree generation of ker π |
| `test_sslib.py` | brute-force self-test of the ℤ/n linear algebra (3000 trials) |
| `verify_examples.py` | 392 checks of the tables and claims of Examples 1.6, 4.2, 4.4–4.7, 4.9, 4.10 and Remark 2.8 |
| `controls.py` | negative and positive controls for the checker |
| `verify_new_examples.py` | Examples 4.11 (dual numbers) and 4.12 (non-reduced algebra, characteristics 0, 2, 3) |
| `check_session_outputs.py` | every generator, lifting and normal form printed in `examples_output.txt` and `regression_output.txt` |
| `crosscheck_v11.py N SEED` | N random cases (polynomial and quotient rings over ℚ, 𝔽₃, ℤ/4, ℤ/6; two gradings) |
| `lean/` | Lean 4 formalization of the order-theoretic lemmas (inherited from the referee's verification package; scope in `lean/lean_report.md`; `lean/check_axioms.sh` recompiles it and lists the axioms used) |

## How to cite

Please cite the paper: A. Abbas and J. A. Khan, *A Lifting Criterion for Subalgebra Standard Bases in Monoid-Graded Rings with Zero Divisors*. Citation metadata is in [`CITATION.cff`](CITATION.cff).

## License

`ssbasis.lib` and the accompanying scripts are free software, distributed under the GNU General Public License, version 3 or (at your option) any later version; see [`LICENSE`](LICENSE).
