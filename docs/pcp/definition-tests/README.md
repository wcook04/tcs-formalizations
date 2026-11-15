# Tests of the definitions behind `np_subset_pcp`

Repository `troyjlee/tcs-formalizations` at a0ce13e, Lean 4.35.0-rc2, Mathlib 065356127b.
Everything below was compiled and run on 14 November 2026. AI agents directed by Will Cook wrote
the tests and ran the edits, and this note is addressed to the author of the repository. No
mathematician has reviewed it.

## What was tested

The question was whether the four modules behind the headline (`PCP/Verifier/Definition.lean`,
`PCP/Complexity/CostModel.lean`, `PCP/Complexity/NP.lean`, `PCP/Complexity/Machine.lean`) mean
what Arora and Barak's Definitions 2.1 and 11.4 mean. The test file,
[`PCP/Audit/DefinitionStressTests/SanityChecks.lean`](../../../PCP/Audit/DefinitionStressTests/SanityChecks.lean),
imports only those four modules and Mathlib. It has 63 theorems, all compiled, each using at
most `propext`, `Classical.choice` and `Quot.sound`. They fall into three groups.

- Longhand contracts: completeness, soundness, acceptance probability, `ReadsBelow`,
  `CanonicalRandomness`, `ImplementedBy`, `PolyTimeAlg` and the NP certificate, each restated
  from the textbook clause and checked against your definition by `Iff.rfl` or `rfl`.
- Small verifiers with exact answers: always accept, always reject, read one bit, match a fair
  coin (every fixed proof wins with probability 1/2, while each coin has a winning proof), a
  verifier whose second address sits only on the `true` branch, and your hidden-budget example
  from `Definition.lean` lines 139–144 as a family over `f`.
- A frozen copy of the headline conclusion (`IntendedHeadline`). The displayed statement at
  `PCP/Theorem.lean` lines 25–33 is definitionally equal to it.

## Mutation table in brief

The agents applied 32 small edits to your files, one at a time, and recompiled the definition
modules and the test file after each. The full table is in [MUTATION_TABLE.md](MUTATION_TABLE.md)
and the edits are the patches in [mutants/](mutants/).

| Group | Example edits | Result |
|---|---|---|
| Caught by a test directly (17) | `∀ π` to `∃ π` in soundness; a proof per coin in completeness; `ImplementedBy` on one input or one seed; `PolyTimeAlg := True`; Boolean outputs encoded as `[]`; all seeds mapped to the zero string; `QueryTree.eval` branches swapped | a named test fails |
| Caught first by your own lemmas (10) | probability normalisation off by a factor of 2; `ReadsBelow` for one seed or with `≤`; addresses from the `false` branch only; `CanonicalRandomness` with `≤`, `True` or a linear budget; pair separator removed; overflow accepts | your lemmas (`accProb_le_one`, `accProb_congr_of_readsBelow`, `CanonicalRandomness.logRandomness`, `ofStep_zero`, `length_encodePair` and others) stop compiling; with only those proofs replaced by `sorry`, a test still fails |
| Edits to the headline (5) | constants chosen after `x`; soundness 1, 0 or −1; `V.queries = q` removed | the frozen statement check rejects each, and so does your proof of `np_subset_pcp` |

No edit survived. The one designed to be harmless, removing `V.queries = q`, fails the strict
check because the statement is a different term; a compiled equivalence shows nothing is lost,
since `queries` is already a field fixed before the input.

## The edit I found most instructive

The edit changes the field to `run : … → QueryTree ((x.length + 2) ^ queries)` and makes
`ImplementedBy` unfold to the same depth. All four modules still compile and the text of
`np_subset_pcp` is unchanged. Under this edit a verifier that reads the whole witness compiles
([M32WholeWitness.lean](M32WholeWitness.lean)):
for a language with exact-length witnesses checked by `R`, and `q` with `p(n) ≤ (n+2)^q`, it
satisfies every clause of the headline conclusion, with the machine certificate for its step
function left as a hypothesis, and with `queries = 1` each of the first `n` proof bits decides its
run on inputs of length `n`. So the statement can keep its shape while constant locality is lost.
In your development the edit is caught by the type of `run`: a one-line test that
`V.run x r : QueryTree V.queries` fails, as do the tests that spell out `ImplementedBy`.

## Conventions the tests record

These follow your definitions and comments; the tests only fix them in place.

- `QueryTree.ofStep` at depth zero turns a further query request into a rejecting leaf
  (`CostModel.lean` lines 41–47), so `ImplementedBy` compares `V.run` with the capped unfolding.
  An algorithm that always queries implements the zero-query rejecting verifier (`rfl`).
- `ReadsBelow` counts addresses on every syntactic branch (`Definition.lean` lines 46–49,
  116–119), including a branch that no fixed oracle can follow.
- `CanonicalRandomness` uses equality for the reason your comment at lines 136–146 gives; an
  explicit budget 0, 1, 0, … meets `LogRandomness 0 1` and is never canonical.
- Threshold 1 is met by every verifier and threshold −1 by none (compiled). For threshold 0 only
  the first step is compiled: soundness 0 holds iff no proof is accepted on any seed.

## What this does not establish

- It does not audit the 749-file proof. The proof was rebuilt here with the pinned toolchain
  (4044 jobs, no errors), and `headline_contract : IntendedHeadline := np_subset_pcp`, the
  converse through `pcp_subset_np_concrete` and `inNP_iff_mem` compile against it, each with
  axioms `propext`, `Classical.choice` and `Quot.sound`. That is a rebuild, not a review.
- No Comparator run was made.
- The step function of the whole-witness verifier has no machine certificate, and the reverse
  direction for the modified class is an argument on paper only. The same holds for the claim
  that threshold 0 gives P and that the hidden budget admits undecidable unary languages.
- The tests compare your definitions with a reading of the textbook made by AI agents and me. A shared misreading would
  pass them.

## Running the tests

With the four definition modules built at a0ce13e:

```
lake env lean PCP/Audit/DefinitionStressTests/SanityChecks.lean
```

Nothing in the repository imports the test file.
