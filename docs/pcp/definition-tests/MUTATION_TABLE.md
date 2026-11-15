# The 32 edits

Each row is one edit to `troyjlee/tcs-formalizations` at a0ce13e, applied on its own with
`patch -p1 --fuzz=0` from the file of the same number in [mutants/](mutants/). After each edit the
changed definition modules, the definition modules after them and the test file were recompiled
with Lean 4.35.0-rc2, and the sources were then restored.

Where a lemma in the repository's own definition module stops compiling, that lemma is named in
the third column. For those rows the proofs of the named lemmas were replaced by `sorry` in a
second pass, and the last column lists the tests that fail in that pass. Edits M26 to M30 change
`PCP/Theorem.lean`; for them the displayed statement is compared with the frozen copy in the test
file, and the repository's proof line was also recompiled and fails under each.

No edit survives.

| ID | Edit | Site | First rejected by | Tests that fail |
|---|---|---|---|---|
| M01 | Add an impossible NP-certificate field | `PCP/Complexity/NP.lean:30` | a test | `all_inNP_of_true_polytime`, `empty_inNP_of_false_polytime`, `all_inNP_inputBlind`, `empty_inNP_inputBlind` |
| M02 | Remove the checking-relation runtime requirement | `PCP/Complexity/NP.lean:36` | a test | `np_checkability_contract`, `all_inNP_of_true_polytime`, `empty_inNP_of_false_polytime`, `all_inNP_inputBlind`, `empty_inNP_inputBlind`, `singleton_not_inNP_inputBlind` |
| M03 | Keep only the positive direction of the NP specification | `PCP/Complexity/NP.lean:38` | a test | `np_spec_contract`, `all_inNP_of_true_polytime`, `empty_inNP_of_false_polytime`, `all_inNP_inputBlind`, `empty_inNP_inputBlind`, `singleton_not_inNP_inputBlind` |
| M04 | Measure the witness bound in its own length | `PCP/Complexity/NP.lean:39` | a test | `np_spec_contract` |
| M05 | Replace all proofs by one proof in soundness | `PCP/Verifier/Definition.lean:134` | a test | `soundness_contract`, `reject_sound_zero`, `every_verifier_sound_at_one`, `no_negative_soundness`, `complete_excludes_sound_below_one`, `matchCoin_sound_half`, `matchCoin_not_sound_zero`, `hidden_budget_sound_zero`, `sound_zero_iff` |
| M06 | Test soundness only on the zero proof | `PCP/Verifier/Definition.lean:134` | a test | `soundness_contract`, `every_verifier_sound_at_one`, `complete_excludes_sound_below_one`, `sound_zero_iff` |
| M07 | Allow the proof to depend on the random seed | `PCP/Verifier/Definition.lean:131` | a test | `completeness_contract`, `accept_complete`, `reject_not_complete`, `complete_excludes_sound_below_one`, `readBit_complete`, `matchCoin_not_complete`, `complete_fixed_proof`, `hidden_budget_complete` |
| M08 | Require only nonnegative acceptance for completeness | `PCP/Verifier/Definition.lean:131` | a test | `completeness_contract`, `accept_complete`, `reject_not_complete`, `complete_excludes_sound_below_one`, `matchCoin_not_complete`, `complete_fixed_proof` |
| M09 | Divide acceptance mass by twice the sample-space size | `PCP/Verifier/Definition.lean:104` | PCP.Verifier.Definition (accProb_le_one, accProb_eq_one_iff) | `acceptance_probability_contract`, `matchCoin_probability`, `sound_zero_iff` |
| M10 | Use the accepting seed count as a probability | `PCP/Verifier/Definition.lean:104` | PCP.Verifier.Definition (accProb_le_one, accProb_eq_one_iff) | `acceptance_probability_contract`, `matchCoin_probability`, `sound_zero_iff` |
| M11 | Require the proof-address bound for only one seed | `PCP/Verifier/Definition.lean:119` | PCP.Verifier.Definition (accProb_congr_of_readsBelow) | `reads_below_contract`, `accept_reads_zero`, `reject_reads_zero`, `readBit_reads_exact`, `true_branch_address_counts`, `every_coin_address_counts` |
| M12 | Ignore the true-answer subtree when collecting addresses | `PCP/Verifier/Definition.lean:49` | PCP.Verifier.Definition (card_addresses_lt_two_pow, eval_congr) | `true_branch_address_counts`, `impossible_branch_still_listed` |
| M13 | Change the strict address bound to an inclusive bound | `PCP/Verifier/Definition.lean:119` | PCP.Verifier.Definition (accProb_congr_of_readsBelow) | `reads_below_contract`, `readBit_reads_exact`, `true_branch_address_counts`, `every_coin_address_counts` |
| M14 | Replace exact canonical randomness by an upper bound | `PCP/Verifier/Definition.lean:155` | PCP.Verifier.Definition (CanonicalRandomness.logRandomness, CanonicalRandomness.eq_closedForm) | `canonical_randomness_contract`, `irregular_never_canonical` |
| M15 | Remove the randomness restriction | `PCP/Verifier/Definition.lean:154` | PCP.Verifier.Definition (CanonicalRandomness.logRandomness, CanonicalRandomness.eq_closedForm) | `canonical_randomness_contract`, `accept_canonical`, `reject_canonical`, `irregular_never_canonical` |
| M16 | Use a computable linear randomness budget | `PCP/Verifier/Definition.lean:155` | PCP.Verifier.Definition (CanonicalRandomness.logRandomness, CanonicalRandomness.eq_closedForm) | `canonical_randomness_contract` |
| M17 | Remove the relation between the certified algorithm and V | `PCP/Complexity/CostModel.lean:63` | a test | `implementation_contract`, `accept_implemented`, `reject_implemented`, `unrelated_algorithm_rejected`, `one_input_is_insufficient_for_implementation`, `one_seed_is_insufficient_for_implementation`, `hidden_budget_implemented` |
| M18 | Require implementation equality on only one input | `PCP/Complexity/CostModel.lean:63` | a test | `implementation_contract`, `accept_implemented`, `reject_implemented`, `unrelated_algorithm_rejected`, `one_input_is_insufficient_for_implementation`, `one_seed_is_insufficient_for_implementation`, `hidden_budget_implemented` |
| M19 | Require implementation equality on only one seed per input | `PCP/Complexity/CostModel.lean:63` | a test | `implementation_contract`, `accept_implemented`, `reject_implemented`, `unrelated_algorithm_rejected`, `one_input_is_insufficient_for_implementation`, `one_seed_is_insufficient_for_implementation`, `hidden_budget_implemented` |
| M20 | Declare every verifier step function polynomial time | `PCP/Complexity/Machine.lean:71` | a test | `concrete_algorithm_contract` |
| M21 | Delete the pair separator | `PCP/Complexity/Machine.lean:35` | PCP.Complexity.Machine (length_encodePair) | `pair_separators_distinguish_positions` |
| M22 | Encode both Boolean outputs as the empty string | `PCP/Complexity/Machine.lean:48` | a test | `distinct_boolean_outputs` |
| M23 | Delete the query tag from algorithm outputs | `PCP/Complexity/Machine.lean:45` | a test | `answer_tags_distinguish_halt_and_query` |
| M24 | Map every random seed to the all-false bit string | `PCP/Complexity/CostModel.lean:28` | a test | `distinct_one_bit_seeds` |
| M25 | Accept instead of rejecting when the query budget is exhausted | `PCP/Complexity/CostModel.lean:44` | PCP.Complexity.CostModel (ofStep_zero) | `overflow_rejects` |
| M26 | Choose the verifier and constants after seeing x | `PCP/Theorem.lean:26` | a test | `candidate_is_frozen` |
| M27 | Replace headline soundness 1/2 by 1 | `PCP/Theorem.lean:33` | a test | `candidate_is_frozen` |
| M28 | Replace headline soundness 1/2 by 0 | `PCP/Theorem.lean:33` | a test | `candidate_is_frozen` |
| M29 | Replace headline soundness 1/2 by -1 | `PCP/Theorem.lean:33` | a test | `candidate_is_frozen` |
| M30 | Delete only the equality naming the existing query bound | `PCP/Theorem.lean:29` | a test | `candidate_is_frozen` |
| M31 | Reverse the true and false branches in query evaluation | `PCP/Verifier/Definition.lean:44` | a test | `readBit_probability`, `matchCoin_probability`, `matchCoin_coinwise_witness` |
| M32 | Interpret the query field as an exponent of an input-dependent budget | `PCP/Verifier/Definition.lean:91; PCP/Complexity/CostModel.lean:64` | a test | `implementation_contract`, `unrelated_algorithm_rejected`, `accept_algorithm_matches_empty_input`, `one_input_is_insufficient_for_implementation`, `accept_algorithm_matches_first_seed`, `one_seed_is_insufficient_for_implementation`, `run_depth_contract` |
