# Quantitative Remainder Transport in Collatz Dynamics

This repository contains a Lean-verified quantitative synthesis of effective
residue transport and positive-density logarithmic-time Collatz convergence.

For every modulus `N ≥ 1`, every residue `r mod N`, and every sufficiently
large scale `X`, the main theorem constructs a finite set `W` of distinct
integers such that every `n ∈ W`

- satisfies `n ≡ r (mod N)`;
- reaches `1` under ordinary Collatz iteration; and
- obeys an explicit numerical upper bound.

The certified count is

```text
|W| ≥ δ X / (2 (ceil((523/50) log X) + 4)),
```

where `δ > 0` and the cutoff are the explicit constants in Mazur's formalized
positive-density theorem.

The general witness bound is

```text
n ≤ (3X + 1) · 2^(2^(48N^4)).
```

Sharper Lean-verified versions cover moduli coprime to `6`, powers of `3`, and
factorized moduli with an explicit residue certificate.

## Main Lean declarations

- `EREQuantitativeTransport.explicit_logarithmic_remainder_transport_ten46`
- `EREQuantitativeTransport.direct_to_one_logarithmic_count_ten46`
- `EREQuantitativeTransport.direct_to_one_count_of_selector`
- `EREQuantitativeTransport.direct_to_one_logarithmic_count_coprime_six`
- `EREQuantitativeTransport.direct_to_one_logarithmic_count_pow_three`
- `EREQuantitativeTransport.direct_to_one_logarithmic_count_factorized`

`QRT.lean` is the project umbrella. `ERE.lean` is restricted to the upstream
Effective Remainder Everywhere base.

## Verification

The release is pinned to:

```text
leanprover/lean4:v4.30.0-rc2
mathlib revision 5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

For every principal QRT theorem, `#print axioms` reports only:

```text
propext, Classical.choice, Quot.sound
```

No `sorry` or `admit` occurs in the audited QRT theorem modules.

## External prerequisite

The first public release does **not** redistribute André Hallqvist's
`EffectiveRemainderEverywhere.lean`, because its public repository currently
contains no explicit redistribution license. See
[`UPSTREAM_HALLQVIST.md`](UPSTREAM_HALLQVIST.md).

Mazur's required formal source closure is included under its Apache-2.0 terms,
with its original `LICENSE` and `NOTICE` retained.

## What this contributes to understanding Collatz

A useful way to picture Collatz is as a huge directed forest: every number has
one forward path, while many possible paths may run backward into the same
target.

Hallqvist's result showed that, if a target is not divisible by `3`, its
backward tree eventually enters every residue class modulo every `N`. In simple
terms, no modular clock position is permanently missing.

Mazur's result showed that a fixed positive proportion of integers reach `1`
quickly—within a constant times `log n` ordinary Collatz steps.

The ten QRT theorem stages connect these two facts quantitatively. They show
that, for every modulus and every chosen remainder, there is not merely one
exceptional integer in that remainder class that reaches `1`. There is an
explicitly growing family of distinct such integers, together with explicit
upper bounds on how large the constructed integers may be.

This changes the picture in three ways:

1. **Modular access is abundant, not merely possible.**  
   Congruence conditions alone cannot isolate a residue class from the
   convergent part of Collatz dynamics.

2. **The main loss is caused by paths merging.**  
   Different quickly convergent targets can lie on the same Collatz orbit and
   therefore produce the same transported witness. The proof controls this
   overlap by the orbit length, which is why the present count contains a
   `log X` denominator.

3. **The next obstruction is now concrete.**  
   To improve the result from roughly `X / log X` witnesses to a positive
   proportion of witnesses in every residue class, it would be enough to
   control this merging multiplicity more strongly—uniformly, on average, or
   on a sufficiently large subfamily.

The theorem therefore does not solve the Collatz conjecture, but it narrows the
search. A future counterexample mechanism cannot be explained simply by saying
that convergent inverse trees avoid certain congruence classes. They do not:
every residue class contains quantitatively many certified starts that reach
`1`.

Natural extensions include improving the enormous effective size bounds,
measuring and bounding orbit-collision multiplicities, comparing the counts in
different residue classes, and ultimately asking whether every residue class
contains a positive-density set of integers that reaches `1`.

## What this does not prove

This work does not prove the Collatz conjecture, density-one convergence, or
positive lower density inside every residue class. The logarithmic denominator
comes from a proved worst-case orbit-fibre multiplicity bound. Removing that
loss is a separate problem.

## Paper

- `paper/Quantitative_Remainder_Transport.pdf`
- `paper/Quantitative_Remainder_Transport.tex`

## Authorship and AI disclosure

Project author: **Shreyas Samir Kolte**.

OpenAI language models accessed through ChatGPT/Codex contributed substantially
to mathematical exploration, Lean proof generation and debugging, repository
preparation, and manuscript drafting. See [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md).

## License

Original QRT Lean source and repository tooling are released under Apache-2.0.
Third-party components retain their respective notices and terms. The paper's
license is stated separately in its release metadata.

