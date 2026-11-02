# External Effective Remainder Everywhere prerequisite

Quantitative Remainder Transport uses André Hallqvist's **Effective Remainder
Everywhere** theorem and Lean formalization as an external prerequisite:

<https://github.com/Sio-MLST/Effective-Remainder-Everywhere>

The upstream repository did not expose an explicit redistribution license when
this QRT release was prepared. Consequently, this repository and its Zenodo
archive do not contain Hallqvist's Lean source and do not purport to relicense
it.

The checked development used a local Lean 4.30 compatibility port of the
upstream file. That port is withheld from this release. The release audit
records the expected local module name:

```text
ERE.EffectiveRemainderEverywhere
```

and the QRT sources import that module. A future release may replace this
external prerequisite with either author-approved redistribution or an
independent formalization.

The mathematical use of Effective Remainder Everywhere is described and cited
in the accompanying paper. Hallqvist is not represented as an author of QRT.

