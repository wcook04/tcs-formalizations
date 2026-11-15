/-
M32 in the small: under the mutated verifier type, a checker that reads the
whole witness satisfies the mutated verifier interface.

This file is compiled ONLY against the M32 mutant of the definition layer:
`PCP/Verifier/Definition.lean` with
  run : (x : List Bool) → Fin (2 ^ randomness x.length) → QueryTree ((x.length + 2) ^ queries)
and `PCP/Complexity/CostModel.lean` with `ImplementedBy` unfolding to depth
`(x.length + 2) ^ V.queries`. Against the original definitions it does not
elaborate, which is the point of the `run_depth_contract` detector.

What is proved here (under the mutant):
* `readAll_guarantee`: if `L x ↔ ∃ w, w.length = p(|x|) ∧ R x w = true` and
  `p(n) ≤ (n + 2) ^ q` for every `n`, the verifier that reads proof bits
  `0, …, p(|x|) - 1` and applies `R` meets every clause of the mutated
  headline conclusion except `Machine.PolyTimeAlg`, which stays a hypothesis.
* `readAll_not_local`: with `queries = 1` and `p = X`, on every input of
  length `n` each of the first `n` proof bits changes the outcome of the
  single run. The field called `queries` is 1; the run reads `n` bits.

Not proved here: a machine certificate for the step function, or the
reverse inclusion for the mutated class. Those remain mathematical arguments.
-/
import PCP.Verifier.Definition
import PCP.Complexity.CostModel
import PCP.Complexity.NP
import PCP.Complexity.Machine
import Mathlib.Tactic

namespace PCP.DefinitionStressTests.M32

/-- Step function of a checker that queries proof bits `0, 1, …, N - 1` in order and then
applies `R` to the bits it has read. -/
def readAllStep (R : List Bool → List Bool → Bool) (N : ℕ) (x : List Bool) :
    List Bool → Bool ⊕ ℕ :=
  fun as => if as.length < N then .inr as.length else .inl (R x as)

/-- The verifier algorithm with that step function. -/
def readAllAlg (R : List Bool → List Bool → Bool) (p : Polynomial ℕ) : VerifierAlg :=
  fun x _ as => readAllStep R (p.eval x.length) x as

/-- The whole-witness verifier, typed under the M32 mutant. -/
def readAllV (R : List Bool → List Bool → Bool) (p : Polynomial ℕ) (q : ℕ) : Verifier where
  randomness := fun _ => 0
  queries := q
  run := fun x _ =>
    QueryTree.ofStep (readAllStep R (p.eval x.length) x) ((x.length + 2) ^ q) []

theorem eval_readAll (R : List Bool → List Bool → Bool) (N : ℕ) (x : List Bool)
    (π : ProofOracle) :
    ∀ (k : ℕ) (as : List Bool), as = (List.range as.length).map π →
      as.length ≤ N → N ≤ as.length + k →
      (QueryTree.ofStep (readAllStep R N x) k as).eval π = R x ((List.range N).map π) := by
  intro k
  induction k with
  | zero =>
    intro as has hle hk
    have hN : as.length = N := by omega
    have hstep : readAllStep R N x as = .inl (R x as) := by
      simp [readAllStep, hN]
    rw [QueryTree.ofStep_zero, hstep]
    simp only [QueryTree.eval]
    rw [← hN]
    exact congrArg (R x) has
  | succ k ih =>
    intro as has hle hk
    by_cases hlt : as.length < N
    · have hstep : readAllStep R N x as = .inr as.length := by
        simp [readAllStep, hlt]
      have hnext : as ++ [π as.length] = (List.range (as ++ [π as.length]).length).map π := by
        rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
        rw [← has]
        simp
      have key := ih (as ++ [π as.length]) hnext (by simp; omega) (by simp; omega)
      simp only [QueryTree.ofStep, hstep, QueryTree.eval]
      cases hπ : π as.length
      · simpa [hπ] using key
      · simpa [hπ] using key
    · have hN : as.length = N := by omega
      have hstep : readAllStep R N x as = .inl (R x as) := by
        simp [readAllStep, hN]
      simp only [QueryTree.ofStep, hstep, QueryTree.eval]
      rw [← hN]
      exact congrArg (R x) has

theorem addresses_readAll (R : List Bool → List Bool → Bool) (N : ℕ) (x : List Bool) :
    ∀ (k : ℕ) (as : List Bool), as.length ≤ N →
      ∀ a ∈ (QueryTree.ofStep (readAllStep R N x) k as).addresses, a < N := by
  intro k
  induction k with
  | zero =>
    intro as _ a ha
    rw [QueryTree.ofStep_zero] at ha
    split at ha <;> simp [QueryTree.addresses] at ha
  | succ k ih =>
    intro as hle a ha
    by_cases hlt : as.length < N
    · have hstep : readAllStep R N x as = .inr as.length := by
        simp [readAllStep, hlt]
      simp only [QueryTree.ofStep, hstep, QueryTree.addresses, Finset.mem_insert,
        Finset.mem_union] at ha
      rcases ha with rfl | ha | ha
      · exact hlt
      · exact ih _ (by simp; omega) a ha
      · exact ih _ (by simp; omega) a ha
    · have hstep : readAllStep R N x as = .inl (R x as) := by
        simp [readAllStep, hlt]
      simp [QueryTree.ofStep, hstep, QueryTree.addresses] at ha

/-- The single run of `readAllV` computes `R` on the first `p(|x|)` proof bits. -/
theorem run_eval (R : List Bool → List Bool → Bool) (p : Polynomial ℕ) (q : ℕ)
    (hq : ∀ n : ℕ, p.eval n ≤ (n + 2) ^ q) (x : List Bool) (r) (π : ProofOracle) :
    ((readAllV R p q).run x r).eval π = R x ((List.range (p.eval x.length)).map π) :=
  eval_readAll R _ x π _ [] (by simp) (by simp) (by simpa [readAllV] using hq x.length)

theorem map_range_oracleOfWitness (w : List Bool) :
    (List.range w.length).map (oracleOfWitness w) = w := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [oracleOfWitness, List.getD_eq_getElem?_getD, h2]

/-- Every clause of the mutated headline conclusion, except the machine certificate for the
step function, which stays a hypothesis. Here `L` has exact-length witnesses checked by `R`. -/
theorem readAll_guarantee (L : Language) (R : List Bool → List Bool → Bool)
    (p : Polynomial ℕ) (q : ℕ)
    (hL : ∀ x, L x ↔ ∃ w : List Bool, w.length = p.eval x.length ∧ R x w = true)
    (hq : ∀ n : ℕ, p.eval n ≤ (n + 2) ^ q)
    (halg : Machine.PolyTimeAlg (readAllAlg R p)) :
    ∃ (V : Verifier) (alg : VerifierAlg) (a b q' : ℕ) (p' : Polynomial ℕ),
      Machine.PolyTimeAlg alg ∧
      V.ImplementedBy alg ∧
      V.queries = q' ∧
      V.CanonicalRandomness a b ∧
      (∀ x : List Bool, V.ReadsBelow x (p'.eval x.length)) ∧
      (∀ x : List Bool, L x → V.CompleteAt x) ∧
      (∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) := by
  refine ⟨readAllV R p q, readAllAlg R p, 0, 0, q, p, halg, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro x r
    rfl
  · intro n
    simp [readAllV]
  · intro x r a ha
    exact addresses_readAll R _ x _ [] (by simp) a ha
  · intro x hx
    obtain ⟨w, hw, hR⟩ := (hL x).mp hx
    refine ⟨oracleOfWitness w, ?_⟩
    rw [Verifier.accProb_eq_one_iff]
    intro r
    rw [run_eval R p q hq, ← hw, map_range_oracleOfWitness]
    exact hR
  · intro x hx π
    have hfalse : ∀ r, ((readAllV R p q).run x r).eval π = false := by
      intro r
      rw [run_eval R p q hq]
      cases h : R x ((List.range (p.eval x.length)).map π)
      · rfl
      · exact absurd ((hL x).mpr ⟨_, by simp, h⟩) hx
    have hempty : (readAllV R p q).acceptingRandomness x π = ∅ := by
      ext r
      simp [Verifier.acceptingRandomness, hfalse r]
    rw [Verifier.accProb, hempty]
    norm_num

/-- The checker "every witness bit is true" with witness length `|x|`. -/
def allTrue : List Bool → List Bool → Bool := fun _ w => w.all id

theorem allTrue_bound : ∀ n : ℕ, (Polynomial.X : Polynomial ℕ).eval n ≤ (n + 2) ^ 1 := by
  intro n
  simp

/-- Locality is lost: `queries = 1`, yet on an input of length `n` each of the first `n` proof
bits decides the single run. -/
theorem readAll_not_local (x : List Bool) (i : ℕ) (hi : i < x.length) (r) :
    (readAllV allTrue Polynomial.X 1).queries = 1 ∧
    ((readAllV allTrue Polynomial.X 1).run x r).eval (fun _ => true) = true ∧
    ((readAllV allTrue Polynomial.X 1).run x r).eval
      (Function.update (fun _ => true) i false) = false := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [run_eval allTrue _ 1 allTrue_bound]
    simp [allTrue]
  · rw [run_eval allTrue _ 1 allTrue_bound]
    simp only [allTrue, Polynomial.eval_X, List.all_eq_false]
    refine ⟨false, ?_, by simp⟩
    simp only [List.mem_map, List.mem_range]
    exact ⟨i, hi, by simp⟩

end PCP.DefinitionStressTests.M32

#print axioms PCP.DefinitionStressTests.M32.readAll_guarantee
#print axioms PCP.DefinitionStressTests.M32.readAll_not_local
