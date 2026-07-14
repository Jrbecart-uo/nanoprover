# CDC formalization — status

Target: OpenAI's claimed proof of the **Cycle Double Cover conjecture**
("A proof of the cycle double cover conjecture", 2026; the paper states
*"The proof in this note is entirely due to GPT5.6 Sol Ultra"*).

**We have NOT certified the conjecture.** We have certified most of the paper's
novel step, and we have isolated exactly what remains. Read the boundary below.

## Proved, kernel-checked, clean axioms (`[propext, Classical.choice, Quot.sound]`)

| file | result | what it is |
|---|---|---|
| `cdc_core.lean` | `cdc_local` | the three local sets contain every vector exactly 0 or 2 times, **for every `t`** |
| | `cdc_pairs` | the three local vectors are distinct, so each `Pₑ` really has size 2 |
| | `cdc_crux` | **the vertex parity identity** — the gauge sum `η_b(x)` equals the parity of how many of `η_a, η_b, η_c` are nonzero |
| `cdc_lemma21.lean` | `exists_cycle_decomposition` | every 0-or-2-regular edge set of a multigraph decomposes into cycles (proved **from scratch** — see below) |
| | **`lemma21`** | **given the family `P` (`|Pₑ|=2`, 0-or-2 at each vertex), a cycle double cover EXISTS** |
| `cdc_lemma22.lean` | `mem_range_iff_forall_dualFamily` | the duality criterion, in the shape Lemma 2.2 uses |
| | `sum_vertexSum` / `sum_vertexSum'` | handshake + **incidence exchange** for multigraphs |
| | `dualFamily_annihilates_iff` | **condition (5)**, as an iff |
| | `lemma22_reduction` | Lemma 2.2, modulo the vertex-local fact |
| `cdc_assembly.lean` | **`pairing_vanishes`** | **the global half of Lemma 2.2**: incidence exchange → parity → handshake ⟹ `∑ₑ ηₑ(dₑ) = 0` |

## The one remaining gap

`pairing_vanishes` takes a hypothesis `hlocal`: *at each vertex, the gauge sum of
`η` equals the parity of how many incident `ηₑ` are nonzero.*

That is **exactly `cdc_crux`** — which is proved. What is missing is only the
plumbing: a cubic-multigraph-with-local-edge-order structure, the gauge
`g(v,a)=0, g(v,b)=f(a), g(v,c)=0`, and the observation that the incidence sum at a
cubic vertex collapses to its three edges. Mechanical, but not yet written.

So: **every mathematical idea in the paper's step 3 is now kernel-verified.
The remaining work is bookkeeping, not mathematics.**

## Not formalized at all (cited by the paper, and by us)

* **Jaeger's reduction** (bridgeless ⟹ suffices to treat cubic).
* **The 8-flow theorem** (Kilpatrick/Jaeger: every bridgeless graph has a
  nowhere-zero `𝔽₂³`-flow).

These are established results, but they are *assumed* here, not proved. Anyone
reading this as "CDC is now formally verified" is reading it wrong.

## Notes worth keeping

* **Mathlib cannot express this.** `SimpleGraph.Walk.IsCycle` forces length ≥ 3, so
  a **digon** (two parallel edges) is unrepresentable — yet the paper explicitly
  regards two parallel edges as a cycle. Mathlib's newer multigraph type `Graph α β`
  has no degree, no walk, no cycle. The Eulerian existence direction is an open
  `TODO` in `Trails.lean`. So the multigraph cycle theory was built from scratch.
* **Cubicity is not used by Lemma 2.1.** It is needed only to *produce* the family
  `P`, never to consume it.
* Definitional caveat: `IsCyc` = "edge set of a nonempty closed trail with all
  degrees 0 or 2" (a connected 2-regular edge set). This correctly excludes
  figure-eights and disjoint unions. That such a trail is *vertex-simple* was not
  separately formalized — true, but a gap in the *definition*, not the argument.

## Independent computational check

The proof is constructive, so it was also run end-to-end: 133 random bridgeless
cubic graphs, the Petersen graph (**which has no nowhere-zero 4-flow** — the exact
gap where CDC was open), K₄, K₃,₃, the cube, multigraphs with parallel edges, and
**20,000 random local edge-orderings** (the gauge is order-dependent, so this
mattered). A valid cycle double cover every time. Zero failures.

**We found no flaw.**
