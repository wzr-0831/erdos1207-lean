# Sources and attribution

- Mathematics: Sungchul Lee, Cosmin Pohoata and Daniel G. Zhu, *The Minkowski
  grid has robustly many repeated distances*, arXiv:2607.05374v1 (2026).
  This is a formalization of their published planar consequence, not a new
  mathematical discovery or an optimal-order result in every dimension.
- NYLL arithmetic proof: Naganori Yamaguchi, assisted by OpenAI Codex;
  Apache-2.0. Extract: n-yamaguchi-0729/SawinTotallyRealTowers commit
  7761174d792fe0e5e91765783eb975513ad0b6b4. The 1,555 imported source files
  match canonical n-yamaguchi-0729/NYLL commit
  8c1b16d10afaca09e0dc72753c6575e230d31a55. Original dependency LICENSE,
  NOTICE and source-specific credits must be retained with that dependency.
- Lower-box proof: Formal Frontier Team, mathlib-initiative/sum_product,
  Apache-2.0, commit80e4127a67742659d521466204c6d2d7e0ca2b3f.
  LowerCountCandidate extracts the relevant Boxes/AdditiveCount proof;
  import narrowing and the Set.equivOfEq API adaptation are the only proof
  compatibility changes. Original source headers remain in the Lean file.
- Frozen definitions: The Formal Conjectures Authors, Apache-2.0.
  FC1207Binding transparently copies exactly five definition/notation blocks
  from FormalConjectures/ErdosProblems/1207.lean and the supporting
  Geometry/Euclidean, Geometry/2d and Data/Set/Triplewise modules. It preserves
  their namespaces, bodies and the complete statement. It is not an import
  or CI run of the original Formal Conjectures4.33.1 project.
- The remaining finite/ideal/geometry/parameter proofs and assembly were
  produced by this AI-assisted formalization project. No unverified human
  identity, first-discovery/formalization priority, award or acceptance is claimed.
- Lean and Mathlib retain their respective upstream licenses and credits.

The source manifests preserve original source hashes and every comment-only
publication edit. No mathematical source body was changed for this package.

The original NYLL notice is retained verbatim in third_party/NYLL-NOTICE.
The complete lower-count compatibility diff is retained in
third_party/lower-count-API-adaptation.patch. The root LICENSE is the
Apache-2.0 license text; all source-specific copyright headers are retained.
