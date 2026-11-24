import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4085 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Finset (Fin (10 : ℕ))) (x5 x6 : Finset ℕ), (∀ (x7 : Fin (10 : ℕ)), ↑x7 ∈ x5 ↔ x7 ∈ x4) → ((10 : ℕ) ∈ x5 ↔ (0 : Fin (10 : ℕ)) ∈ x4) → (∀ (x9 : Fin x1.size), ∀ x10 ∈ (x1.gates.get x9).inputs, ((11 : ℕ) + ↑x9 ∈ x5 → x10 ∈ x5) ∧ ((11 : ℕ) + ↑x9 ∉ x5 → x10 ∈ x5 → x10 ∈ x6)) → (x1.output ∈ x5 → x1.output ∈ x6) → [(1 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (12 : ℕ), (9 : ℕ), (9 : ℕ), (5 : ℕ), (3 : ℕ), (2 : ℕ)].getD x4.card (0 : ℕ) ≤ (Finset.image (fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ↥x6) => (x1.wires (List.ofFn x11 ++ [!x11 (0 : Fin (10 : ℕ))])).getD (↑x12) Bool.false) Finset.univ).card) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) x5 := by
  intro C hC hs H
  by_contra hne
  push_neg at hne
  have h1 := H Finset.univ (Finset.range (11 + C.size)) {C.output}
  simp_all
