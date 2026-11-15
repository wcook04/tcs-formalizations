/-
Definition stress tests for the PCP definition layer of troyjlee/tcs-formalizations
at a0ce13e. Compiled natively with Lean 4.35.0-rc2 and the pinned Mathlib
(14 Nov 2026); every theorem's axioms are within propext, Classical.choice,
Quot.sound. Each test is tied to a mutant in the mutation table or to a
textbook clause. The file imports only the four definition modules and
Mathlib.Tactic, never PCP.Theorem or the proof development.
-/
import PCP.Verifier.Definition
import PCP.Complexity.CostModel
import PCP.Complexity.NP
import PCP.Complexity.Machine
import Mathlib.Tactic

namespace PCP.DefinitionStressTests

/-! ## Independent longhand contracts

The right-hand sides below deliberately spell out the intended semantics.
The declarations are small elaboration checks, not proofs of field convention.
-/

theorem acceptance_probability_contract (V : Verifier) (x : List Bool) (π : ProofOracle) :
    V.accProb x π =
      ((V.acceptingRandomness x π).card : ℚ) / ((2 : ℚ) ^ V.randomness x.length) := rfl

theorem completeness_contract (V : Verifier) (x : List Bool) :
    V.CompleteAt x ↔ ∃ π : ProofOracle, V.accProb x π = 1 := Iff.rfl

theorem soundness_contract (V : Verifier) (x : List Bool) (s : ℚ) :
    V.SoundAt x s ↔ ∀ π : ProofOracle, V.accProb x π ≤ s := Iff.rfl

theorem reads_below_contract (V : Verifier) (x : List Bool) (N : ℕ) :
    V.ReadsBelow x N ↔ ∀ r, ∀ a ∈ (V.run x r).addresses, a < N := Iff.rfl

theorem canonical_randomness_contract (V : Verifier) (a b : ℕ) :
    V.CanonicalRandomness a b ↔
      ∀ n : ℕ, V.randomness n = a * Nat.clog 2 (n + 2) + b := Iff.rfl

theorem implementation_contract (V : Verifier) (alg : VerifierAlg) :
    V.ImplementedBy alg ↔
      ∀ (x : List Bool) (r : Fin (2 ^ V.randomness x.length)),
        QueryTree.ofStep (alg x (bitsOfFin (V.randomness x.length) r)) V.queries [] =
          V.run x r := Iff.rfl

theorem concrete_algorithm_contract (alg : VerifierAlg) :
    Machine.PolyTimeAlg alg ↔
      Nonempty (Turing.TM2ComputableInPolyTime Machine.encodeTriple Machine.encodeAnswer
        (fun t => alg t.1 t.2.1 t.2.2)) := Iff.rfl

theorem np_spec_contract (P : (List Bool → List Bool → Bool) → Prop) (L : Language)
    (c : NPCertificate P L) (x : List Bool) :
    L x ↔ ∃ w : List Bool, w.length ≤ c.witnessBound.eval x.length ∧ c.check x w = true :=
  c.spec x

theorem np_checkability_contract (P : (List Bool → List Bool → Bool) → Prop)
    (L : Language) (c : NPCertificate P L) : P c.check := c.check_polyTime

def acceptV : Verifier where
  randomness := fun _ => 0
  queries := 0
  run := fun _ _ => .leaf true

def rejectV : Verifier where
  randomness := fun _ => 0
  queries := 0
  run := fun _ _ => .leaf false

def acceptAlg : VerifierAlg := fun _ _ _ => .inl true
def rejectAlg : VerifierAlg := fun _ _ _ => .inl false

/-- Helper (added natively): if every run returns `b` on `π`, the probability is `1` or `0`. -/
theorem accProb_of_constant (V : Verifier) (x : List Bool) (π : ProofOracle) (b : Bool)
    (h : ∀ r, (V.run x r).eval π = b) : V.accProb x π = if b then 1 else 0 := by
  cases b
  · have hempty : V.acceptingRandomness x π = ∅ := by
      ext r
      simp [Verifier.acceptingRandomness, h r]
    simp [Verifier.accProb, hempty]
  · simpa using (V.accProb_eq_one_iff x π).mpr h

theorem accept_probability (x : List Bool) (π : ProofOracle) :
    acceptV.accProb x π = 1 := by
  simpa using accProb_of_constant acceptV x π true (fun _ => rfl)

theorem reject_probability (x : List Bool) (π : ProofOracle) :
    rejectV.accProb x π = 0 := by
  simpa using accProb_of_constant rejectV x π false (fun _ => rfl)

theorem accept_complete (x : List Bool) : acceptV.CompleteAt x :=
  ⟨fun _ => false, accept_probability x _⟩

theorem reject_sound_zero (x : List Bool) : rejectV.SoundAt x 0 := by
  intro π
  simp [reject_probability]

theorem reject_not_complete (x : List Bool) : ¬ rejectV.CompleteAt x := by
  rintro ⟨π, h⟩
  rw [reject_probability] at h
  norm_num at h

theorem accept_canonical : acceptV.CanonicalRandomness 0 0 := by
  intro n
  simp [acceptV]

theorem reject_canonical : rejectV.CanonicalRandomness 0 0 := by
  intro n
  simp [rejectV]

theorem accept_reads_zero (x : List Bool) : acceptV.ReadsBelow x 0 := by
  intro r a ha
  simp [acceptV, QueryTree.addresses] at ha

theorem reject_reads_zero (x : List Bool) : rejectV.ReadsBelow x 0 := by
  intro r a ha
  simp [rejectV, QueryTree.addresses] at ha

theorem accept_implemented : acceptV.ImplementedBy acceptAlg := by
  intro x r
  rfl

theorem reject_implemented : rejectV.ImplementedBy rejectAlg := by
  intro x r
  rfl

theorem unrelated_algorithm_rejected : ¬ acceptV.ImplementedBy rejectAlg := by
  intro h
  have htree := h [] ⟨0, by decide⟩
  have hbool := congrArg (fun T : QueryTree 0 => T.eval (fun _ => false)) htree
  change false = true at hbool
  cases hbool

/-- This semantic verifier accepts only the empty input and uses no proof bits. -/
def inputDependentV : Verifier where
  randomness := fun _ => 0
  queries := 0
  run := fun x _ => .leaf x.isEmpty

theorem accept_algorithm_matches_empty_input :
    ∀ r : Fin 1,
      QueryTree.ofStep (acceptAlg [] (bitsOfFin 0 r)) inputDependentV.queries [] =
        inputDependentV.run [] r := by
  intro r
  rfl

theorem one_input_is_insufficient_for_implementation :
    ¬ inputDependentV.ImplementedBy acceptAlg := by
  intro h
  have htree := h [false] ⟨0, by decide⟩
  have hbool := congrArg (fun T : QueryTree 0 => T.eval (fun _ => false)) htree
  change true = false at hbool
  cases hbool

/-- This semantic verifier accepts one of its two seeds and uses no proof bits. -/
def seedDependentV : Verifier where
  randomness := fun _ => 1
  queries := 0
  run := fun _ r => .leaf (decide (r.val = 0))

theorem accept_algorithm_matches_first_seed (x : List Bool) :
    QueryTree.ofStep (acceptAlg x (bitsOfFin 1 ⟨0, by decide⟩)) seedDependentV.queries [] =
      seedDependentV.run x ⟨0, by simp [seedDependentV]⟩ := rfl

theorem one_seed_is_insufficient_for_implementation :
    ¬ seedDependentV.ImplementedBy acceptAlg := by
  intro h
  have htree := h [] ⟨1, by decide⟩
  have hbool := congrArg (fun T : QueryTree 0 => T.eval (fun _ => false)) htree
  change true = false at hbool
  cases hbool

theorem every_verifier_sound_at_one (V : Verifier) (x : List Bool) :
    V.SoundAt x 1 := fun π => V.accProb_le_one x π

theorem no_negative_soundness (V : Verifier) (x : List Bool)
    (s : ℚ) (hs : s < 0) : ¬ V.SoundAt x s := by
  intro h
  have hnonneg := V.accProb_nonneg x (fun _ => false)
  have hupper := h (fun _ => false)
  linarith

theorem complete_excludes_sound_below_one (V : Verifier) (x : List Bool)
    (s : ℚ) (hs : s < 1) (hc : V.CompleteAt x) : ¬ V.SoundAt x s := by
  obtain ⟨π, hπ⟩ := hc
  intro h
  have hupper := h π
  rw [hπ] at hupper
  exact (not_le_of_gt hs) hupper

def readBitV (a : ℕ) : Verifier where
  randomness := fun _ => 0
  queries := 1
  run := fun _ _ => .query a (.leaf false) (.leaf true)

theorem readBit_probability (a : ℕ) (x : List Bool) (π : ProofOracle) :
    (readBitV a).accProb x π = if π a then 1 else 0 :=
  accProb_of_constant (readBitV a) x π (π a) (fun _ => by
    cases h : π a <;> simp [readBitV, QueryTree.eval, h])

theorem readBit_complete (a : ℕ) (x : List Bool) : (readBitV a).CompleteAt x := by
  refine ⟨fun _ => true, ?_⟩
  simp [readBit_probability]

theorem readBit_has_rejecting_proof (a : ℕ) (x : List Bool) :
    ∃ π : ProofOracle, (readBitV a).accProb x π ≤ (1 / 2 : ℚ) := by
  refine ⟨fun _ => false, ?_⟩
  norm_num [readBit_probability]

theorem readBit_reads_exact (a N : ℕ) (x : List Bool) :
    (readBitV a).ReadsBelow x N ↔ a < N := by
  constructor
  · intro h
    exact h ⟨0, by simp [readBitV]⟩ a (by simp [readBitV, QueryTree.addresses])
  · intro h r j hj
    have hj' : j = a := by simpa [readBitV, QueryTree.addresses] using hj
    simpa [hj'] using h

/-- Address 1 occurs only in the true-answer branch. -/
def hiddenTrueBranchV : Verifier where
  randomness := fun _ => 0
  queries := 2
  run := fun _ _ =>
    .query 0 (.leaf false) (.query 1 (.leaf false) (.leaf true))

theorem true_branch_address_counts (x : List Bool) :
    ¬ hiddenTrueBranchV.ReadsBelow x 1 := by
  intro h
  have hbad := h ⟨0, by simp [hiddenTrueBranchV]⟩ 1
    (by simp [hiddenTrueBranchV, QueryTree.addresses])
  exact (Nat.lt_irrefl 1) hbad

/-- Address 1 occurs only under the second coin. -/
def secondCoinAddressV : Verifier where
  randomness := fun _ => 1
  queries := 1
  run := fun _ r =>
    if r.val = 0 then .leaf false else .query 1 (.leaf false) (.leaf true)

theorem every_coin_address_counts (x : List Bool) :
    ¬ secondCoinAddressV.ReadsBelow x 1 := by
  intro h
  have hbad := h ⟨1, by simp [secondCoinAddressV]⟩ 1
    (by simp [secondCoinAddressV, QueryTree.addresses])
  exact (Nat.lt_irrefl 1) hbad

/-- The one proof bit must equal the fair coin. Each fixed proof wins half the time. -/
def matchCoinV : Verifier where
  randomness := fun _ => 1
  queries := 1
  run := fun _ r =>
    .query 0 (.leaf (decide (r.val = 0))) (.leaf (decide (r.val = 1)))

theorem matchCoin_probability (x : List Bool) (π : ProofOracle) :
    matchCoinV.accProb x π = (1 / 2 : ℚ) := by
  have e : ∀ r : Fin (2 ^ matchCoinV.randomness x.length),
      ((matchCoinV.run x r).eval π = true ↔ r.val = (if π 0 then 1 else 0)) := by
    intro r
    cases h : π 0 <;> simp [matchCoinV, QueryTree.eval, h]
  have hcard : (matchCoinV.acceptingRandomness x π).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨⟨if π 0 then 1 else 0, by split <;> simp [matchCoinV]⟩, ?_⟩
    ext r
    simp [Verifier.acceptingRandomness, e r, Fin.ext_iff]
  rw [Verifier.accProb, hcard]
  norm_num [matchCoinV]

theorem matchCoin_coinwise_witness (x : List Bool) :
    ∀ r : Fin 2, ∃ π : ProofOracle, (matchCoinV.run x r).eval π = true := by
  intro r
  fin_cases r
  · exact ⟨fun _ => false, rfl⟩
  · exact ⟨fun _ => true, rfl⟩

theorem matchCoin_not_complete (x : List Bool) : ¬ matchCoinV.CompleteAt x := by
  rintro ⟨π, h⟩
  rw [matchCoin_probability] at h
  norm_num at h

theorem matchCoin_sound_half (x : List Bool) : matchCoinV.SoundAt x (1 / 2) := by
  intro π
  simp [matchCoin_probability]

theorem matchCoin_not_sound_zero (x : List Bool) : ¬ matchCoinV.SoundAt x 0 := by
  intro h
  have hfalse := h (fun _ => false)
  rw [matchCoin_probability] at hfalse
  norm_num at hfalse

/-- This regression retains a genuine fixed oracle across all coins. -/
theorem complete_fixed_proof (V : Verifier) (x : List Bool) :
    V.CompleteAt x ↔ ∃ π : ProofOracle, ∀ r, (V.run x r).eval π = true := by
  constructor
  · rintro ⟨π, hπ⟩
    exact ⟨π, (V.accProb_eq_one_iff x π).mp hπ⟩
  · rintro ⟨π, hπ⟩
    exact ⟨π, (V.accProb_eq_one_iff x π).mpr hπ⟩

theorem distinct_one_bit_seeds :
    bitsOfFin 1 ⟨0, by decide⟩ ≠ bitsOfFin 1 ⟨1, by decide⟩ := by
  decide

theorem overflow_rejects (a : ℕ) :
    QueryTree.ofStep (fun _ => .inr a) 0 [] = (QueryTree.leaf false : QueryTree 0) := rfl

/-- Repeated queries use the same oracle, rather than independent answer bits. -/
def contradictoryPathTree : QueryTree 2 :=
  .query 0 (.leaf false) (.query 0 (.leaf true) (.leaf false))

theorem repeated_address_is_consistent (π : ProofOracle) :
    contradictoryPathTree.eval π = false := by
  cases h : π 0 <;> simp [contradictoryPathTree, QueryTree.eval, h]

/-- All syntactic branches contribute, even a path no fixed oracle can follow. -/
def impossibleBranchTree : QueryTree 3 :=
  .query 0 (.leaf false)
    (.query 0 (.query 17 (.leaf true) (.leaf true)) (.leaf false))

theorem impossible_branch_still_listed : 17 ∈ impossibleBranchTree.addresses := by
  simp [impossibleBranchTree, QueryTree.addresses]

theorem impossible_branch_never_reached (π : ProofOracle) :
    impossibleBranchTree.eval π = false := by
  cases h : π 0 <;> simp [impossibleBranchTree, QueryTree.eval, h]

/-! The next family mechanises the budget side channel described by the author
at Verifier/Definition.lean:139–144. It does not add a machine certificate for
`budgetLengthAlg`. That native obligation is explicit below. -/

def hiddenBudgetV (f : ℕ → Bool) : Verifier where
  randomness := fun n => if f n then 1 else 0
  queries := 0
  run := fun x _ => .leaf (f x.length)

def budgetLengthAlg : VerifierAlg :=
  fun _ r _ => .inl (decide (r.length = 1))

theorem hidden_budget_log_bounded (f : ℕ → Bool) :
    (hiddenBudgetV f).LogRandomness 0 1 := by
  intro n
  change (if f n then 1 else 0) ≤ 0 * Nat.clog 2 (n + 2) + 1
  cases h : f n <;> simp [h]

theorem hidden_budget_implemented (f : ℕ → Bool) :
    (hiddenBudgetV f).ImplementedBy budgetLengthAlg := by
  intro x r
  cases h : f x.length <;>
    simp [hiddenBudgetV, budgetLengthAlg, QueryTree.ofStep, bitsOfFin, h]

theorem hidden_budget_probability (f : ℕ → Bool) (x : List Bool) (π : ProofOracle) :
    (hiddenBudgetV f).accProb x π = if f x.length then 1 else 0 :=
  accProb_of_constant (hiddenBudgetV f) x π (f x.length) (fun _ => rfl)

theorem hidden_budget_complete (f : ℕ → Bool) (x : List Bool)
    (hf : f x.length = true) : (hiddenBudgetV f).CompleteAt x := by
  refine ⟨fun _ => false, ?_⟩
  simp [hidden_budget_probability, hf]

theorem hidden_budget_sound_zero (f : ℕ → Bool) (x : List Bool)
    (hf : f x.length = false) : (hiddenBudgetV f).SoundAt x 0 := by
  intro π
  simp [hidden_budget_probability, hf]

/-- An explicitly noncanonical budget: 0,1,0 at lengths 0,1,2. -/
def irregularV : Verifier where
  randomness := fun n => if n = 1 then 1 else 0
  queries := 0
  run := fun _ _ => .leaf true

theorem irregular_log_bounded : irregularV.LogRandomness 0 1 := by
  intro n
  change (if n = 1 then 1 else 0) ≤ 0 * Nat.clog 2 (n + 2) + 1
  split_ifs <;> simp

theorem irregular_never_canonical (a b : ℕ) : ¬ irregularV.CanonicalRandomness a b := by
  intro h
  have h1 := h 1
  have h2 := h 2
  have hc3 : Nat.clog 2 3 = 2 := by decide
  have hc4 : Nat.clog 2 4 = 2 := by decide
  norm_num [irregularV, hc3, hc4] at h1 h2
  omega

/-- A scalar typing check. Under a polynomial-depth reinterpretation this fails. -/
def run_depth_contract (V : Verifier) (x : List Bool)
    (r : Fin (2 ^ V.randomness x.length)) : QueryTree V.queries := V.run x r

theorem pair_separators_distinguish_positions :
    Machine.encodePair ([], [false]) ≠ Machine.encodePair ([false], []) := by
  decide

theorem answer_tags_distinguish_halt_and_query (b : Bool) (a : ℕ) :
    Machine.encodeAnswer (.inl b) ≠ Machine.encodeAnswer (.inr a) := by
  simp [Machine.encodeAnswer]

theorem distinct_boolean_outputs : Machine.encodeBool false ≠ Machine.encodeBool true := by
  decide

/-- Explicit native machine obligation. This lemma does not discharge that obligation. -/
theorem all_inNP_of_true_polytime
    (h : Machine.PolyTimeRel (fun _ _ => true)) :
    InNP Machine.PolyTimeRel (fun _ => True) := by
  refine ⟨⟨0, fun _ _ => true, h, ?_⟩⟩
  intro x
  constructor
  · intro _
    exact ⟨[], by simp, rfl⟩
  · intro _
    trivial

/-- Explicit native machine obligation. This lemma does not discharge that obligation. -/
theorem empty_inNP_of_false_polytime
    (h : Machine.PolyTimeRel (fun _ _ => false)) :
    InNP Machine.PolyTimeRel (fun _ => False) := by
  refine ⟨⟨0, fun _ _ => false, h, ?_⟩⟩
  intro x
  constructor
  · intro hfalse
    exact False.elim hfalse
  · rintro ⟨w, _, hfalse⟩
    cases hfalse

/-- A genuinely restricted relation class: the checker ignores the input. -/
def InputBlindRel (R : List Bool → List Bool → Bool) : Prop :=
  ∀ x y w, R x w = R y w

theorem all_inNP_inputBlind : InNP InputBlindRel (fun _ => True) := by
  refine ⟨⟨0, fun _ _ => true, fun _ _ _ => rfl, ?_⟩⟩
  intro x
  constructor
  · intro _
    exact ⟨[], by simp, rfl⟩
  · intro _
    trivial

theorem empty_inNP_inputBlind : InNP InputBlindRel (fun _ => False) := by
  refine ⟨⟨0, fun _ _ => false, fun _ _ _ => rfl, ?_⟩⟩
  intro x
  constructor
  · intro hfalse
    exact False.elim hfalse
  · rintro ⟨w, _, hfalse⟩
    cases hfalse

/-- Same-length inputs cannot be distinguished even when the witness bound varies with length. -/
theorem singleton_not_inNP_inputBlind :
    ¬ InNP InputBlindRel (fun x => x = [true]) := by
  rintro ⟨c⟩
  obtain ⟨w, hw, hc⟩ := (c.spec [true]).mp rfl
  have hc' : c.check [false] w = true := (c.check_polyTime [false] [true] w).trans hc
  have hbad : ([false] : List Bool) = [true] :=
    (c.spec [false]).mpr ⟨w, by simpa using hw, hc'⟩
  cases hbad

/-! ## The headline conclusion as a frozen predicate (moved here from NativeIntegration)

These need only the definition layer. `IntendedHeadline` is the frozen statement that
`headline_contract` and the generated headline probe compare against. -/

def GuaranteeAt (s : ℚ) (L : Language) : Prop :=
  ∃ (V : Verifier) (alg : VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),
    Machine.PolyTimeAlg alg ∧
    V.ImplementedBy alg ∧
    V.queries = q ∧
    V.CanonicalRandomness a b ∧
    (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧
    (∀ x : List Bool, L x → V.CompleteAt x) ∧
    (∀ x : List Bool, ¬ L x → V.SoundAt x s)

/-- The explicit type, including global witness order and the literal threshold. -/
def IntendedHeadline : Prop :=
  ∀ (L : Language), InNP Machine.PolyTimeRel L → GuaranteeAt (1 / 2) L

/-- Naming the fixed query field by an existential `q` adds no restriction (M30 control). -/
theorem redundant_query_name (V : Verifier) (A : Prop) :
    (∃ q : ℕ, V.queries = q ∧ A) ↔ A := by
  constructor
  · rintro ⟨q, _, h⟩
    exact h
  · intro h
    exact ⟨V.queries, rfl, h⟩

/-- Added natively: soundness 0 says no proof is accepted on any seed (first step of the
"threshold 0 gives P" argument; the polynomial-time decider itself is not formalised). -/
theorem sound_zero_iff (V : Verifier) (x : List Bool) :
    V.SoundAt x 0 ↔ ∀ (π : ProofOracle) r, (V.run x r).eval π = false := by
  constructor
  · intro h π r
    have h0 : V.accProb x π = 0 := le_antisymm (h π) (V.accProb_nonneg x π)
    have hpos : (0 : ℚ) < 2 ^ V.randomness x.length := by positivity
    have hcard : (V.acceptingRandomness x π).card = 0 := by
      rw [Verifier.accProb, div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 hpos.ne'
    rw [Finset.card_eq_zero] at hcard
    have hr : r ∉ V.acceptingRandomness x π := by simp [hcard]
    simpa [Verifier.acceptingRandomness] using hr
  · intro h π
    rw [accProb_of_constant V x π false (h π)]
    simp

end PCP.DefinitionStressTests
