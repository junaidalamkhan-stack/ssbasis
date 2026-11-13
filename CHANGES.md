# Changes

## Version 1.2 (November 2026)

**New default: the reduction test**

* `SSliftingTest(G,W)` and `SSliftingData(G,W)` now use the reduction test of Corollary 3.5. For every homogeneous generator u of ker π, ψ(u) is S-reduced; F is an SS-basis iff every ψ(u) reduces to 0. A reduction ending at 0 gives the printed lifting; otherwise the nonzero normal form reached is printed (without the words "NO lifting"). Only ker π is computed, which avoids the elimination for ker ψ: a random case over ℤ₆[x,y]/(y³) that took more than 20 s now takes about 0.01 s.
* The lifting test of version 1.1 (Lemma 4.1(a)) is still available with an optional third argument: `SSliftingTest(G,W,1)`, `SSliftingData(G,W,1)`. With it the library reproduces the stored outputs of version 1.1 exactly. Both tests give the same verdict.
* `SScomplete` uses the reduction test.

**Corrected**

* In a `qring` over ℤ whose ideal contains a constant (coefficients effectively ℤ/m), Singular 4.3.2 can leave terms with coefficient 0 after a multiplication; such a term could be taken for a leading term. They are now removed (`ssClean`).

**Input validation**

* Non-commutative baserings and ring parameters named `Y1`, `Y2`, … now raise an ERROR.

**Supplementary material**

* `examples/examples_output.txt` and `tests/regression_output.txt` regenerated with Singular 4.3.2. All verdicts are unchanged. Differences from version 1.1: the reduction test prints "psi(u) has the nonzero normal form …" instead of "NO lifting; …"; two liftings differ (Example 4.2(ii) of the paper now prints Y2+3Y3+Y4, the lifting given in the paper, and Example 4.3 prints another valid lifting); line numbers in ERROR traces moved.
* `verification/check_session_outputs.py` checks every lifting and normal form in the new outputs (all checks pass).
* `verification/crosscheck_v11.py` takes an optional third argument (0 = reduction test, 1 = lifting test), recognizes the output of the reduction test, and also compares the overall verdict with the exhaustive test. 1200 random cases in each mode: no mismatches (`out_crosscheck_v11.txt`).

## Version 1.1 (revision of October 2026)

**Corrected**

* *Quotient rings.* Version 1.0 copied the quotient ideal of the basering into the auxiliary ring of the variables Yᵢ. In ℚ[x,y]/(x²), for example, the ideal (x²) became (Y₁²), and the code certified {y+xy} as an SS-basis although it is not. It also printed the invalid lifting `Y1^2` in 𝔽₂[x,y]/(x²). Version 1.1 builds the auxiliary rings without a quotient, includes the quotient ideal I explicitly in the eliminations (I + ⟨Yᵢ − fᵢ⟩, I + ⟨Yᵢ − Υ(fᵢ)⟩), and reduces every input polynomial modulo I before computing degrees and leading forms.
* *Input validation.* Version 1.0 performed no validation: it accepted, for instance, a negative weight (so that Γ = ℤ is not well-ordered) and printed a verdict. Version 1.1 raises an ERROR for every unsupported input (see README).

**New**

* `SScomplete(G,W,b)`: Algorithm 1 of the paper with a bound on the number of passes. Its reduction step decides membership of a leading form in S[Υ(F)] by a normal form modulo a standard basis of I + ⟨Yᵢ − Υ(fᵢ)⟩ for an elimination order (Lemma 4.1(b) of the paper). The procedure was adapted from a verification implementation written during refereeing, then extended to quotient rings and degree-0 variables, and retested (`examples/`, `tests/`, `verification/`).
* When no lifting exists, `SSliftingTest` now prints a nonzero S-normal form of ψ(u), which is the element Algorithm 1 adjoins.
* `SSliftingData(G,W)`: the results as a list, for use in scripts.
* Variables with a zero column in `W` are treated as degree-0 variables belonging to S = R₀. This makes coefficient rings such as ℚ[y] or the dual numbers available.
* Kernel generators are split into Ω-homogeneous components and reduced modulo the degree-zero part of the quotient ideal.

**Supplementary material**

* `examples/examples.sing` reproduces every session of the revised manuscript; `examples/integer_groebner.sing` contains the strong Gröbner basis computation over ℤ used in Example 4.4.
* `tests/regression.sing`: quotient rings (Q1–Q5), degree-0 variables and constants (Z1–Z7), a parameter field (P1), and one test for each class of unsupported input (R1–R9).
* `verification/`: independent checks in Python, including a randomized comparison with version 1.0 as a negative control.

**Unchanged**

* The interface `SSliftingTest(G,W)` with an `intmat W`, the helper procedures `ssLexCmp`, `ssExpDeg`, `ssNatural`, `ssLex`, and the output format, apart from the wording "SS-basis" and the extra line for non-liftable generators.
* The lifting test itself: reduction modulo a standard basis of ker ψ for a global order refining Ω. Version 1.1 computes ker ψ by explicit elimination; the running time on the paper's examples is unchanged.

## Version 1.0

Procedures `ssLexCmp`, `ssExpDeg`, `ssPolyDeg`, `ssLeadForm`, `ssNatural`, `ssLex`, `SSliftingTest` (polynomial rings only).
