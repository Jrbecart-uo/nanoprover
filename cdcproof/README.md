# CDCProof — a lake project tying the CDC verification together

Builds the five verification modules against the local Mathlib checkout
(`../mathlib4`, toolchain `v4.32.0-rc1`) so they cross-import as real modules,
rather than the standalone REPL files in `../verification/`.

```
lake build          # ~60s warm (reuses mathlib's prebuilt oleans)
```

## Modules

| module | content |
|---|---|
| `CDCProof/Core.lean` | the finite `𝔽₂³` facts: `cdc_crux`, `cdc_crux_dual`, self-duality, `cdc_local`, `cdc_pairs` |
| `CDCProof/Multigraph.lean` | multigraph cycle theory (built from scratch) + `lemma21` (family `P` ⟹ CDC) |
| `CDCProof/Duality.lean` | dual-annihilator criterion, handshake, `lemma22_reduction` |
| `CDCProof/Glue.lean` | `CubicFlow`, `hlocal`, `pairing_vanishes_cubic` |
| `CDCProof/Main.lean` | the capstone (in progress) |

Every result is kernel-checked with clean axioms (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorry`, no `native_decide`.

**This certifies the paper's novel step 3, NOT the conjecture.** Jaeger's
reduction to cubic graphs and the 8-flow theorem are cited, not formalized.
See `../verification/STATUS.md`.
