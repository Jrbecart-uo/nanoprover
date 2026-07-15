# CDC formalization — status

**UPDATE 2026-07-15: the single end-to-end capstone theorem is now proved.**
`CDCProof.cdc_of_cubicFlow` (in `cdcproof/CDCProof/Main.lean`):

    theorem cdc_of_cubicFlow (G : CF.CubicFlow V E) :
        ∃ 𝒞 : Multiset (Finset E), G.toMG.IsCDC 𝒞

*Every cubic flow graph has a cycle double cover.*  Clean axioms
`[propext, Classical.choice, Quot.sound]` — no `sorry`, no `native_decide`.
A `CubicFlow` is a loopless cubic multigraph with a chosen local edge order and
a nowhere-zero `𝔽₂³`-flow.  The five modules build together as one lake project
(`cdcproof/`) against the local Mathlib checkout.

The proof chains: solve Lemma 2.2's linear system (`exists_solution`, via the
duality reduction + `pairing_vanishes_cubic`) → build the edge family `P` →
`|P_e| = 2` and condition (1) (`local_02`, from `cdc_local`) → `lemma21` → CDC.

**Still cited, not proved (unchanged):** Jaeger's reduction of bridgeless graphs
to the cubic case, and the 8-flow theorem (every bridgeless graph has a
nowhere-zero `𝔽₂³`-flow).  So `cdc_of_cubicFlow` certifies the paper's *entire
novel argument* — the reduction of a nowhere-zero `𝔽₂³`-flow to a cycle double
cover — but NOT the two classical inputs it stands on.  This is not a full
certification of the conjecture.

---

**UPDATE 2026-07-15b: the 8-flow half reduced to its combinatorial core.**
`CDCProof.cdc_of_covering` (in `cdcproof/CDCProof/Flow.lean`, clean axioms):

    a cubic graph with a local edge order + three edge-indicators
    `w : Fin 3 → E → 𝔽₂` that are EVEN at every vertex and COVER every edge
      ⟹  a cycle double cover.

A nowhere-zero `𝔽₂³`-flow *is* three even subgraphs covering every edge (each
coordinate is an `𝔽₂`-flow = even subgraph; nowhere-zero = covering).  So this
strips all flow/`𝔽₂³` arithmetic out of the capstone's hypothesis, leaving a
purely combinatorial statement.

What the 8-flow theorem then reduces to (NOT formalized): *every bridgeless
cubic multigraph has three even subgraphs covering its edges.*  This is genuine
graph theory and is **not** cheaply reachable in Mathlib: Mathlib's matching /
Tutte theory is all on `SimpleGraph`, which cannot express the parallel edges
this proof needs (a digon must be a cycle), and there is no nowhere-zero-flow,
cycle-space, or even-subgraph-cover theory at all.  Formalizing it — and
Jaeger's reduction of bridgeless graphs to the cubic case — would require
building multigraph flow/matching infrastructure from scratch: a large,
separate undertaking, not an afternoon's work.

---

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

## The gap is now CLOSED (`cdc_glue.lean`, 2026-07-15)

`pairing_vanishes` took a hypothesis `hlocal`: *at each vertex, the gauge sum of
`η` equals the parity of how many incident `ηₑ` are nonzero.*  That hypothesis is
now **proved** (`hlocal` in `cdc_glue.lean`), and chained through the handshake to
`pairing_vanishes_cubic`.  Clean axioms, no `sorry`, no `native_decide`.

New in `cdc_glue.lean`:
* `cdc_crux_dual` — `cdc_crux` transported from `G3` elements to functionals
  `η : Dual 𝔽₂ G3`, via the self-duality `dotL`/`exists_dot_eq`/`dotL_eq_zero_iff`.
* `CubicFlow` — a loopless cubic multigraph with a chosen local edge order and a
  nowhere-zero `𝔽₂³`-flow (conservation at each vertex).
* `vertexSum'_collapse` — a cubic vertex's incidence sum collapses to its three
  incident edges (uses looplessness: no edge is incident on both sides).
* **`hlocal`** — the vertex-local identity: gauge sum `= η_b(x) =` parity count.
  The one place the cubic structure, gauge, flow, and `cdc_crux` all meet.
* **`pairing_vanishes_cubic`** — for any `CubicFlow` and any dual family `η`
  satisfying condition (5), `∑_e η_e(d_e) = 0` (d built from the gauge).  Exactly
  the hypothesis `lemma22_reduction` consumes.

**So every link of the paper's novel step 3 is now individually kernel-proved.**
The only reason there is no single `theorem cdc : ...` is the standalone-REPL
limitation (each file re-imports Mathlib; there is no lake project tying the five
files into one module). That is packaging, not mathematics.

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

### Adversarial pass (the one that mattered)

Two "break the proof" subagents were launched; **both died on API 529 errors**, so
the hostile review was run by hand instead. The decisive test is **real snarks** —
bridgeless cubic graphs with **no nowhere-zero 4-flow**, i.e. exactly the graphs
where the classical "4-flow ⟹ CDC" argument fails and the conjecture was actually
open:

| graph | 4-flow? | trials | result |
|---|---|---|---|
| Petersen (10v) | **no** | 3,000 + 20,000 orderings | CDC every time |
| Flower snark J₅ (20v) | **no** | 200 | CDC every time |
| Flower snark J₇ (28v) | **no** | 100 | CDC every time |
| Flower snark J₉ (36v) | — | 60 | CDC every time |
| 133 random bridgeless cubic | mixed | 133 | CDC every time |
| multigraphs (theta, doubled edges) | — | 1,000 | CDC every time |

Lemma 2.2's linear system was **never once infeasible**.

**We found no flaw.** Attack surfaces checked: the gauge's dependence on an
arbitrary local edge ordering (20,000 random orderings — no effect); parallel
edges and digons; the duality reduction to condition (5) (traced by hand); the
vertex parity identity (kernel-verified); Lemma 2.1 in multigraphs (formalized).
NOT checked: Jaeger's cubic reduction and the 8-flow theorem, both cited.
