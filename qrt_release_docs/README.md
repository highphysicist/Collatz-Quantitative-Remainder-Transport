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

