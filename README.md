# A verified formalization of the precise planar Erdős1207 bound

```lean
JSP1012.Solution.erdos_1207_statement :
  ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    (Erdos1207.P 2 n : ℝ) < (n : ℝ) ^ (1 - c)
```

This closed theorem has no extra mathematical hypotheses. `P` is the Nat
infimum, over n-point Euclidean sets, of the maximal isosceles-free subset
size. Equally spaced collinear triples are forbidden, as in the published
Lee–Pohoata–Zhu result and the exact frozen Formal Conjectures statement.
The original definitions are transparently licensed excerpts; no upstream
placeholder theorem is imported or used.

## Checked result and exact packaging status

All67 original source modules compiled under official Lean4.35.0-rc2 and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55. Full exact signatures and an
explicit original-statement type ascription passed trust0. Independent actual
proof/type-body traversal found only propext, Classical.choice and Quot.sound,
with no unsafe/partial dependency. Official `leanchecker --fresh --verbose
JSP1012Solution` passed exit0 on2026-10-27 at00:51:10UTC; immutable source,
output and runtime checks then passed. See verification/ for the actual reports.

This inspection copy changes only five comments to remove a local path and
obsolete operational hold notes. SOURCE_MANIFEST.json proves every byte
outside Lean comments is identical to the checked originals and lists both
source hashes. All **67 exact editorial source copies were separately recompiled** into a
new initially empty output tree, finishing successfully on 2026-10-27 at
01:20:52 UTC. ExactTypes (trust0) and independent actual proof/type-body axiom
checks against those new public outputs passed by 01:22:10 UTC; their logs
are byte-identical to the original verified reports. See
`verification/public-copy-qa.json` for this completed packaging check.
The full fresh-kernel replay cited above was performed on the **original
sources**, whose non-comment bytes are identical to these public copies; it
was not repeated for the editorial copies. The included portable Lake layout
is **still not build-tested**. The historical original-verification summary
is retained unchanged; the new public-copy QA report records the updated
exact-copy compilation status.
Historical source-only preparation comments in the proof sources describe
creation time; the completed check results above supersede those old notes.
No already-sealed raw verification evidence has been rewritten.

The proposed portable project pins the same toolchain, Mathlib and the audited
SawinTotallyRealTowers dependency. Every flat local module is an explicit
library root. A clean portable build and generated root manifest remain to be
checked before claiming this exact package has a successful Lake build.
No generated root lake-manifest.json is fabricated here.

This formalizes the published **planar polynomial saving**. It does not solve
the broader optimal-order estimation question in every dimension, establish
priority or award eligibility, or assert acceptance/publication. Mathematical
and licensed source credits are in THIRD_PARTY.md and retained source headers.
