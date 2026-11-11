# Changes

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
