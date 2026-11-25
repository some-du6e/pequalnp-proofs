import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6380_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (6126 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

abbrev BE : BinaryTree ℕ := BinaryTree.nil
abbrev BN (v : ℕ) (l r : BinaryTree ℕ) : BinaryTree ℕ := BinaryTree.node v l r
abbrev BL (v : ℕ) : BinaryTree ℕ := BinaryTree.node v BinaryTree.nil BinaryTree.nil

def InTree (x : ℕ) : BinaryTree ℕ → Prop
  | BinaryTree.nil => False
  | BinaryTree.node v l r => x = v ∨ InTree x l ∨ InTree x r

def treeMem (x : ℕ) : BinaryTree ℕ → Bool
  | BinaryTree.nil => false
  | BinaryTree.node v l r =>
    if x == v then true
    else if x < v then treeMem x l
    else treeMem x r

theorem treeMem_imp {x : ℕ} : ∀ t : BinaryTree ℕ, treeMem x t = true → InTree x t
  | BinaryTree.nil, h => by simp [treeMem] at h
  | BinaryTree.node v l r, h => by
    unfold treeMem at h
    by_cases h1 : x == v
    · exact Or.inl (beq_iff_eq.mp h1)
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : x < v
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inl (treeMem_imp l h))
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inr (treeMem_imp r h))

def checkTree (f : ℕ → Bool) : BinaryTree ℕ → Bool
  | BinaryTree.nil => true
  | BinaryTree.node v l r => f v && checkTree f l && checkTree f r

theorem checkTree_node {f : ℕ → Bool} {v : ℕ} {l r : BinaryTree ℕ}
    (hv : f v = true) (hl : checkTree f l = true) (hr : checkTree f r = true) :
    checkTree f (BN v l r) = true := by
  simp [checkTree, hv, hl, hr]

theorem checkTree_sound {f : ℕ → Bool} : ∀ t : BinaryTree ℕ, checkTree f t = true → ∀ x, InTree x t → f x = true
  | BinaryTree.nil, _, _, hx => hx.elim
  | BinaryTree.node v l r, h, x, hx => by
    simp only [checkTree, Bool.and_eq_true] at h
    rcases hx with rfl | hl | hr
    · exact h.1.1
    · exact checkTree_sound l h.1.2 x hl
    · exact checkTree_sound r h.2 x hr

def freeM (S : Finset ℕ) (v : ℕ) : Prop := v = 0 ∨ v = 65535 ∨ v ∈ S

def combM : Fin 2 → ℕ → ℕ → ℕ
  | 0, a, b => a &&& b
  | 1, a, b => a ||| b

def CanM (f : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => freeM S f
  | k+1, S => ∃ (o : Fin 2) (a b : ℕ), freeM S a ∧ freeM S b ∧ CanM f k (insert (combM o a b) S)

theorem freeMMono {v : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hv : freeM S v) : freeM T v :=
  hv.imp_right (Or.imp_right (fun e => h e))

theorem freeMSub {S T : Finset ℕ} (h : ∀ x ∈ S, freeM T x) {v : ℕ} (hv : freeM S v) : freeM T v := by
  rcases hv with rfl | rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact h v hv

theorem monoCM_free {f k : ℕ} {S T : Finset ℕ} (h : ∀ x ∈ S, freeM T x) (hc : CanM f k S) : CanM f k T := by
  induction k generalizing S T with
  | zero => exact freeMSub h hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    refine ⟨o, a, b, freeMSub h ha, freeMSub h hb, ih ?_ hh⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
    · exact freeMMono (Finset.subset_insert _ _) (h x hx)

theorem monoCM {f k : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hc : CanM f k S) : CanM f k T :=
  monoCM_free (fun x hx => Or.inr (Or.inr (h hx))) hc

theorem stepUpM {f k : ℕ} {S : Finset ℕ} (hc : CanM f k S) : CanM f (k+1) S :=
  ⟨0, 0, 0, Or.inl rfl, Or.inl rfl, monoCM (Finset.subset_insert _ _) hc⟩

theorem smallM {f k : ℕ} {S : Finset ℕ} (hc : CanM f k S) :
    ∃ T ⊆ S, T.card ≤ k+1 ∧ CanM f k T := by
  induction k generalizing S with
  | zero =>
    rcases hc with h | h | h
    · exact ⟨∅, by simp, by simp, Or.inl h⟩
    · exact ⟨∅, by simp, by simp, Or.inr (Or.inl h)⟩
    · exact ⟨{f}, by simpa, by simp, Or.inr (Or.inr (by simp))⟩
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    let v := combM o a b
    obtain ⟨T, hT, hn, hc'⟩ := ih hh
    change T ⊆ insert v S at hT
    by_cases hv : v ∈ T
    · let U := T.erase v ∪ ({a, b} ∩ S)
      have hu : T.erase v ⊆ S := by
        intro x hx
        exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
      have hU : U ⊆ S := Finset.union_subset hu Finset.inter_subset_right
      have liftWire : ∀ w ∈ ({a, b} : Finset ℕ), freeM S w → freeM U w := by
        intro w hw he
        exact he.imp_right (Or.imp_right (fun h => Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw, h⟩)))
      have hcard := Finset.card_union_le (T.erase v) ({a, b} ∩ S)
      have hpair := Finset.card_le_card (Finset.inter_subset_left : ({a, b} ∩ S) ⊆ {a, b})
      have htwo : ({a, b} : Finset ℕ).card ≤ 2 := by
        calc
          _ ≤ ({b} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
          _ = _ := by simp
      rw [Finset.card_erase_of_mem hv] at hcard
      refine ⟨U, hU, by dsimp [U]; omega, o, a, b, liftWire a (by simp) ha, liftWire b (by simp) hb, monoCM ?_ hc'⟩
      intro x hx
      by_cases e : x = v
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e, hx⟩)))
    · refine ⟨T, ?_, by omega, stepUpM hc'⟩
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun e => hv (e ▸ hx))

theorem agreeM {f k a b : ℕ} {S : Finset ℕ} (hb16 : b < 16) (hc : CanM f k S)
    (hs : ∀ v ∈ S, v.testBit a = true → v.testBit b = true) :
    f.testBit a = true → f.testBit b = true := by
  have h65535 : ∀ i < 16, (65535 : ℕ).testBit i = true := by
    intro i hi
    exact (show ∀ j : Fin 16, (65535 : ℕ).testBit j.val = true by decide) ⟨i, hi⟩
  induction k generalizing S with
  | zero =>
    rcases hc with rfl | rfl | h
    · simp
    · intro _; exact h65535 b hb16
    · exact hs _ h
  | succ k ih =>
    have w {v} (hv : freeM S v) : v.testBit a = true → v.testBit b = true := by
      rcases hv with rfl | rfl | h
      · simp
      · intro _; exact h65535 b hb16
      · exact hs _ h
    obtain ⟨o, x, y, hx, hy, hh⟩ := hc
    have hg : (combM o x y).testBit a = true → (combM o x y).testBit b = true := by
      fin_cases o
      · intro h
        simp only [combM, Nat.testBit_land, Bool.and_eq_true] at h ⊢
        exact ⟨w hx h.1, w hy h.2⟩
      · intro h
        simp only [combM, Nat.testBit_lor, Bool.or_eq_true] at h ⊢
        exact h.imp (w hx) (w hy)
    apply ih hh
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact hg
    · exact hs _ h

def gtM : GateOp → List ℕ → ℕ
  | GateOp.and, [] => 65535
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | _, _ => 0

def tstepM (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gtM g.op (g.inputs.map fun i => T.getD i 0)]

def tabsM (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl tstepM T0

def GOkM (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem gtM_testBit (p : Fin 16) (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (l : List ℕ) (hl : l.length ≤ 2) :
    (gtM op l).testBit p.val = op.eval (l.map fun t => t.testBit p.val) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have h6 : (65535 : ℕ).testBit p.val = true :=
    (show ∀ q : Fin 16, (65535 : ℕ).testBit q.val = true by decide) p
  match l, hl with
  | [], _ => rcases hop with rfl | rfl <;> simp [gtM, GateOp.eval, h6]
  | [a], _ => rcases hop with rfl | rfl <;> simp [gtM, GateOp.eval]
  | [a, b], _ => rcases hop with rfl | rfl <;> simp [gtM, GateOp.eval]

theorem gtM_bit_false (p : ℕ) (hp : 16 ≤ p) (op : GateOp) (l : List ℕ)
    (hl : ∀ x ∈ l, x.testBit p = false) : (gtM op l).testBit p = false := by
  have h6 : (65535 : ℕ).testBit p = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by decide) hp))
  cases op <;> cases l with
  | nil => simp [gtM, h6]
  | cons a t =>
    cases t with
    | nil => simp [gtM, hl a (by simp)]
    | cons b t' => simp [gtM, hl a (by simp), hl b (by simp)]

theorem getD_map_testBitM (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]

theorem wires_tabsM (p : Fin 16) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOkM g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p.val)
        = (tabsM T0 gs).map fun t => t.testBit p.val := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p.val) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p.val).getD i false)]
        = (tstepM T0 g).map fun t => t.testBit p.val := by
      simp only [tstepM, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gtM_testBit p g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBitM T0 p.val i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

theorem tabsM_bit_false (p : ℕ) (hp : 16 ≤ p) :
    ∀ (gs : List Gate) (T0 : List ℕ),
      (∀ t ∈ T0, t.testBit p = false) →
      ∀ t ∈ tabsM T0 gs, t.testBit p = false := by
  intro gs
  induction gs with
  | nil => intro T0 hT0; exact hT0
  | cons g gs ih =>
    intro T0 hT0
    apply ih (tstepM T0 g)
    intro t ht
    simp only [tstepM, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hT0 t ht
    · apply gtM_bit_false p hp g.op
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [List.getD_eq_getElem?_getD]
      cases h : T0[i]? with
      | none => simp
      | some v => exact hT0 v (List.mem_of_getElem? h)

theorem getWireM (T : List ℕ) (i : ℕ) : freeM T.toFinset (T.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : T[i]? with
  | none => exact Or.inl rfl
  | some t => exact Or.inr (Or.inr (List.mem_toFinset.mpr (List.mem_of_getElem? h)))

theorem gateChoiceM (T : List ℕ) (g : Gate) (hg : GOkM g) :
    ∃ (o : Fin 2) (a b : ℕ), freeM T.toFinset a ∧ freeM T.toFinset b ∧
      gtM g.op (g.inputs.map fun i => T.getD i 0) = combM o a b := by
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  generalize g.inputs = ins at hl ⊢
  have z : freeM T.toFinset 0 := Or.inl rfl
  have u : freeM T.toFinset 65535 := Or.inr (Or.inl rfl)
  match ins, hl with
  | [], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨1, 65535, 0, u, z, by simp [gtM, combM]⟩
    · exact ⟨1, 0, 0, z, z, rfl⟩
  | [i], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨1, _, 0, getWireM T i, z, by simp [gtM, combM]⟩
    · exact ⟨1, _, 0, getWireM T i, z, by simp [gtM, combM]⟩
  | [i, j], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨0, _, _, getWireM T i, getWireM T j, rfl⟩
    · exact ⟨1, _, _, getWireM T i, getWireM T j, rfl⟩

theorem fromTabsM (f : ℕ) (gs : List Gate) (T : List ℕ) (ok : ∀ g ∈ gs, GOkM g)
    (h : freeM (tabsM T gs).toFinset f) : CanM f gs.length T.toFinset := by
  induction gs generalizing T with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨o, a, b, ha, hb, e⟩ := gateChoiceM T g (ok g (by simp))
    have hh := ih (tstepM T g) (fun g' hg' => ok _ (by simp [hg'])) h
    refine ⟨o, a, b, ha, hb, ?_⟩
    rw [← e]
    simpa [tstepM] using hh

def cuts : ℕ → List ℕ → List (List ℕ)
  | _, [] => [[]]
  | k, x :: xs => if (x :: xs).length ≤ k then [x :: xs] else
      match k with
      | 0 => [[]]
      | j+1 => (cuts j xs).map (x :: ·) ++ cuts (j+1) xs
termination_by _ l => l.length

theorem cutsSpec (k : ℕ) (l : List ℕ) (T : Finset ℕ) (h : T ⊆ l.toFinset) (n : T.card ≤ k) :
    ∃ U ∈ cuts k l, T ⊆ U.toFinset := by
  induction l generalizing k T with
  | nil => exact ⟨[], by simp [cuts], h⟩
  | cons x xs ih =>
    cases k with
    | zero =>
      have he : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨[], by simp [cuts], by simp [he]⟩
    | succ j =>
      rw [cuts]
      split
      · exact ⟨_, by simp, h⟩
      ·
        by_cases hx : x ∈ T
        · have hs : T.erase x ⊆ xs.toFinset := by
            intro y hy
            have hh := h (Finset.mem_of_mem_erase hy)
            simpa [Finset.ne_of_mem_erase hy] using hh
          obtain ⟨U, hU, sub⟩ := ih j (T.erase x) hs (by rw [Finset.card_erase_of_mem hx]; omega)
          refine ⟨x::U, List.mem_append_left _ (List.mem_map.mpr ⟨U, hU, rfl⟩), ?_⟩
          intro y hy
          by_cases e : y = x
          · simp [e]
          · simpa [e] using sub (Finset.mem_erase.mpr ⟨e, hy⟩)
        · have hs : T ⊆ xs.toFinset := by
            intro y hy
            have e : y ≠ x := fun he => hx (he ▸ hy)
            simpa [e] using h hy
          obtain ⟨U, hU, sub⟩ := ih (j+1) T hs n
          exact ⟨U, List.mem_append_right _ hU, sub⟩

theorem cuts_mem_sub : ∀ (l : List ℕ) (k : ℕ) (U : List ℕ), U ∈ cuts k l → ∀ y ∈ U, y ∈ l
  | [], k, U, hU, y, hy => by simp [cuts] at hU; subst hU; simp at hy
  | z :: zs, k, U, hU, y, hy => by
    unfold cuts at hU
    split at hU
    · simp at hU; subst hU; exact hy
    · cases k with
      | zero => simp at hU; subst hU; simp at hy
      | succ j =>
        simp only [List.mem_append, List.mem_map] at hU
        rcases hU with ⟨V, hV, rfl⟩ | hU
        · rcases List.mem_cons.mp hy with rfl | hy
          · simp
          · exact List.mem_cons_of_mem _ (cuts_mem_sub zs j V hV y hy)
        · exact List.mem_cons_of_mem _ (cuts_mem_sub zs (j + 1) U hU y hy)

def sepFold (p0Mask a : ℕ) (U : List ℕ) : ℕ :=
  U.foldl (fun acc v => if v.testBit a then acc &&& v else acc) p0Mask

theorem sepFold_bit_true (a b : ℕ) : ∀ (U : List ℕ) (acc : ℕ),
    (U.foldl (fun acc v => if v.testBit a then acc &&& v else acc) acc).testBit b = true →
    acc.testBit b = true ∧ ∀ v ∈ U, v.testBit a = true → v.testBit b = true
  | [], acc, h => ⟨h, by simp⟩
  | v :: vs, acc, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨hstep, hvs⟩ := sepFold_bit_true a b vs _ h
    by_cases hva : v.testBit a = true
    · simp only [hva, ↓reduceIte, Nat.testBit_land, Bool.and_eq_true] at hstep
      refine ⟨hstep.1, fun w hw hwa => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hstep.2
      · exact hvs w hw hwa
    · simp only [hva, ↓reduceIte] at hstep
      refine ⟨hstep, fun w hw hwa => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact absurd hwa hva
      · exact hvs w hw hwa

def sepOk (p1List : List ℕ) (p0Mask : ℕ) (U : List ℕ) : Bool :=
  p1List.all fun a => sepFold p0Mask a U == 0

theorem coveredM {f k : ℕ} {p1List : List ℕ} {p0Mask : ℕ} {U : List ℕ}
    (hc : CanM f k U.toFinset)
    (hp1 : ∀ a ∈ p1List, f.testBit a = true)
    (hp0 : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ f.testBit b = false) :
    sepOk p1List p0Mask U = true := by
  rw [sepOk, List.all_eq_true]
  intro a ha
  rw [beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.zero_testBit]
  cases htb : (sepFold p0Mask a U).testBit b with
  | false => rfl
  | true =>
    obtain ⟨hb0, hall⟩ := sepFold_bit_true a b U p0Mask htb
    have hfa := hp1 a ha
    have ⟨hb16, hfb⟩ := hp0 b hb0
    have hfb' := agreeM hb16 hc (fun v hv => hall v (List.mem_toFinset.mp hv)) hfa
    exact absurd (hfb'.symm.trans hfb) (by decide)

def insOne (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x == y then y :: ys else if x < y then x :: y :: ys else y :: insOne x ys

def sortU : List ℕ → List ℕ
  | [] => []
  | x :: xs => insOne x (sortU xs)

theorem mem_insOne (x z : ℕ) : ∀ l : List ℕ, z ∈ insOne x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insOne]
  | y :: ys => by
    unfold insOne
    by_cases h1 : x == y
    · simp only [h1, ↓reduceIte]
      have hxy := beq_iff_eq.mp h1; subst hxy; simp
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : x < y
      · simp only [h2, ↓reduceIte]; simp
      · simp only [h2, ↓reduceIte]; simp [mem_insOne x z ys]; tauto

theorem mem_sortU (z : ℕ) : ∀ l : List ℕ, z ∈ sortU l ↔ z ∈ l
  | [] => by simp [sortU]
  | x :: xs => by simp [sortU, mem_insOne, mem_sortU z xs]

def pack : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 65536 * pack xs

def unpack (n : ℕ) : List ℕ :=
  if n = 0 then []
  else (n &&& 65535) :: unpack (n >>> 16)
termination_by n
decreasing_by
  have h1 : n >>> 16 = n / 65536 := Nat.shiftRight_eq_div_pow n 16
  omega

theorem unpack_lt : ∀ (n x : ℕ), x ∈ unpack n → x < 65536 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro x hx
    unfold unpack at hx
    by_cases h0 : n = 0
    · simp [h0] at hx
    · simp only [h0, ↓reduceIte, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      · have hlt : n >>> 16 < n := by
          have h1 : n >>> 16 = n / 65536 := Nat.shiftRight_eq_div_pow n 16
          omega
        exact ih (n >>> 16) hlt x hx

theorem unpack_pack : ∀ l : List ℕ, (∀ x ∈ l, 0 < x ∧ x < 65536) → unpack (pack l) = l
  | [], _ => by unfold unpack; simp [pack]
  | x :: xs, hl => by
    have hx := hl x (by simp)
    have hne : x + 65536 * pack xs ≠ 0 := by omega
    rw [pack, unpack]
    simp only [hne, ↓reduceIte]
    have hlo : (x + 65536 * pack xs) &&& 65535 = x := by
      rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have hhi : (x + 65536 * pack xs) >>> 16 = pack xs := by
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [hlo, hhi, unpack_pack xs (fun y hy => hl y (by simp [hy]))]

def normList (U : List ℕ) : List ℕ :=
  sortU (U.filter (fun x => decide (0 < x) && decide (x < 65535)))

def packSet (U : List ℕ) : ℕ := pack (normList U)

theorem normList_bounds (U : List ℕ) : ∀ x ∈ normList U, 0 < x ∧ x < 65536 := by
  intro x hx
  rw [normList, mem_sortU, List.mem_filter] at hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  omega

theorem unpack_packSet (U : List ℕ) : unpack (packSet U) = normList U :=
  unpack_pack (normList U) (normList_bounds U)

theorem freeM_packSet {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) :
    ∀ x ∈ U.toFinset, freeM (unpack (packSet U)).toFinset x := by
  intro x hx
  have hxm := List.mem_toFinset.mp hx
  have hlt := hU x hxm
  by_cases h0 : x = 0
  · exact Or.inl h0
  · by_cases h1 : x = 65535
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_)
      rw [unpack_packSet, List.mem_toFinset, normList, mem_sortU, List.mem_filter]
      exact ⟨hxm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩

def opPairsM : List ℕ → List ℕ
  | [] => []
  | a :: t => t.flatMap (fun b => [a &&& b, a ||| b]) ++ opPairsM t

theorem mem_opPairsM : ∀ (w : List ℕ) (a b : ℕ), a ∈ w → b ∈ w →
    a &&& b ∈ w ++ opPairsM w ∧ a ||| b ∈ w ++ opPairsM w
  | [], _, _, ha, _ => by simp at ha
  | x :: t, a, b, ha, hb => by
    simp only [List.mem_cons] at ha hb
    simp only [opPairsM, List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false]
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact ⟨Or.inl (Or.inl (Nat.and_self _)), Or.inl (Or.inl (Nat.or_self _))⟩
    · exact ⟨Or.inr (Or.inl ⟨b, hb, Or.inl rfl⟩), Or.inr (Or.inl ⟨b, hb, Or.inr rfl⟩)⟩
    · exact ⟨Or.inr (Or.inl ⟨a, ha, Or.inl (Nat.land_comm _ _)⟩),
             Or.inr (Or.inl ⟨a, ha, Or.inr (Nat.lor_comm _ _)⟩)⟩
    · have ih := mem_opPairsM t a b ha hb
      simp only [List.mem_append] at ih
      refine ⟨?_, ?_⟩
      · rcases ih.1 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
      · rcases ih.2 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

def valsNew (S : List ℕ) : List ℕ :=
  ((opPairsM S).filter (fun v => decide (0 < v) && decide (v < 65535) && !S.contains v)).eraseDups

theorem and_65535_of_lt {x : ℕ} (hx : x < 65536) : x &&& 65535 = x := by
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hx

theorem or_65535_of_lt {x : ℕ} (hx : x < 65536) : x ||| 65535 = 65535 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor]
  by_cases hi : i < 16
  · have h6 : (65535 : ℕ).testBit i = true :=
      (show ∀ j : Fin 16, (65535 : ℕ).testBit j.val = true by decide) ⟨i, hi⟩
    simp [h6]
  · have h2 : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have hx0 : x.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx h2)
    have h60 : (65535 : ℕ).testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) h2)
    simp [hx0, h60]

theorem combM_lt {o : Fin 2} {a b : ℕ} (ha : a < 65536) (hb : b < 65536) : combM o a b < 65536 := by
  fin_cases o
  · exact Nat.and_lt_two_pow (n := 16) a hb
  · exact Nat.or_lt_two_pow (n := 16) ha hb

theorem combM_case {S : List ℕ} (hS : ∀ x ∈ S, x < 65536) {o : Fin 2} {a b : ℕ}
    (ha : freeM S.toFinset a) (hb : freeM S.toFinset b) :
    freeM S.toFinset (combM o a b) ∨ combM o a b ∈ valsNew S := by
  have free_lt {w : ℕ} (hw : freeM S.toFinset w) : w < 65536 := by
    rcases hw with rfl | rfl | h
    · decide
    · decide
    · exact hS w (List.mem_toFinset.mp h)
  have hlt : combM o a b < 65536 := combM_lt (free_lt ha) (free_lt hb)
  rcases ha with rfl | rfl | ha'
  · left; fin_cases o
    · simp only [combM, Nat.zero_and]; exact Or.inl rfl
    · simp only [combM, Nat.zero_or]; exact hb
  · left; fin_cases o
    · simp only [combM, Nat.land_comm 65535, and_65535_of_lt (free_lt hb)]; exact hb
    · simp only [combM, Nat.lor_comm 65535, or_65535_of_lt (free_lt hb)]; exact Or.inr (Or.inl rfl)
  · rcases hb with rfl | rfl | hb'
    · left; fin_cases o
      · simp only [combM, Nat.and_zero]; exact Or.inl rfl
      · simp only [combM, Nat.or_zero]; exact Or.inr (Or.inr ha')
    · left; fin_cases o
      · simp only [combM, and_65535_of_lt (hS _ (List.mem_toFinset.mp ha'))]; exact Or.inr (Or.inr ha')
      · simp only [combM, or_65535_of_lt (hS _ (List.mem_toFinset.mp ha'))]; exact Or.inr (Or.inl rfl)
    · have haL := List.mem_toFinset.mp ha'
      have hbL := List.mem_toFinset.mp hb'
      have hpair := mem_opPairsM S a b haL hbL
      have hmem : combM o a b ∈ S ∨ combM o a b ∈ opPairsM S := by
        fin_cases o
        · exact List.mem_append.mp hpair.1
        · exact List.mem_append.mp hpair.2
      by_cases h0 : combM o a b = 0
      · exact Or.inl (Or.inl h0)
      · by_cases h1 : combM o a b = 65535
        · exact Or.inl (Or.inr (Or.inl h1))
        · by_cases hin : combM o a b ∈ S
          · exact Or.inl (Or.inr (Or.inr (List.mem_toFinset.mpr hin)))
          · right
            rcases hmem with h | hop
            · exact absurd h hin
            · simp only [valsNew, List.mem_eraseDups, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
              refine ⟨hop, ⟨by omega, by omega⟩, ?_⟩
              cases hc : S.contains (combM o a b) with
              | false => rfl
              | true => exact absurd (List.contains_iff_mem.mp hc) hin

theorem can1M_case {f : ℕ} {S : List ℕ} (hS : ∀ x ∈ S, x < 65536) (hc : CanM f 1 S.toFinset) :
    freeM S.toFinset f ∨ f ∈ valsNew S := by
  obtain ⟨o, a, b, ha, hb, h0⟩ := hc
  rcases h0 with rfl | rfl | hm
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · rcases Finset.mem_insert.mp hm with rfl | hf
    · exact combM_case hS ha hb
    · exact Or.inl (Or.inr (Or.inr hf))

def permWGo : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | idx :: rest, k, w => (((w >>> idx) &&& 1) <<< k) ||| permWGo rest (k + 1) w

def permW (p : List ℕ) (w : ℕ) : ℕ := permWGo p 0 w

theorem permWGo_testBit : ∀ (p : List ℕ) (k w i : ℕ),
    (permWGo p k w).testBit i =
      if k ≤ i ∧ i - k < p.length then w.testBit (p.getD (i - k) 0) else false
  | [], k, w, i => by simp [permWGo]
  | idx :: rest, k, w, i => by
    simp only [permWGo, Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_land, Nat.testBit_shiftRight,
      permWGo_testBit rest (k + 1) w i]
    by_cases hlt : i < k
    · have h1 : ¬ k ≤ i := by omega
      have h2 : ¬ k + 1 ≤ i := by omega
      simp [h1, h2]
    · by_cases heq : i = k
      · subst heq
        have h2 : ¬ i + 1 ≤ i := by omega
        simp [h2]
      · have hgt : k + 1 ≤ i := by omega
        have hge : k ≤ i := by omega
        have h1f : (1 : ℕ).testBit (i - k) = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega)))
        have hlen : i - k < (idx :: rest).length ↔ i - (k + 1) < rest.length := by simp; omega
        have hget : (idx :: rest).getD (i - k) 0 = rest.getD (i - (k + 1)) 0 := by
          cases hd : i - k with
          | zero => omega
          | succ m =>
            have hm : i - (k + 1) = m := by omega
            simp [hm]
        simp only [hge, hgt, h1f, Bool.and_false, Bool.false_or, decide_true, Bool.true_and, true_and, ↓reduceIte, hlen, hget]

theorem permW_testBit (p : List ℕ) (hp : p.length = 16) (w i : ℕ) :
    (permW p w).testBit i = if i < 16 then w.testBit (p.getD i 0) else false := by
  simp [permW, permWGo_testBit, hp]

theorem permW_zero (p : List ℕ) (hp : p.length = 16) : permW p 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; simp [permW_testBit p hp]

theorem permW_all (p : List ℕ) (hp : p.length = 16) (hb : ∀ x ∈ p, x < 16) : permW p 65535 = 65535 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [permW_testBit p hp]
  by_cases hi : i < 16
  · simp only [hi, ↓reduceIte]
    have hgi : p.getD i 0 < 16 := by
      rw [List.getD_eq_getElem?_getD]
      cases hg : p[i]? with
      | none => decide
      | some v => exact hb v (List.mem_of_getElem? hg)
    have h6 : ∀ j < 16, (65535 : ℕ).testBit j = true := fun j hj =>
      (show ∀ q : Fin 16, (65535 : ℕ).testBit q.val = true by decide) ⟨j, hj⟩
    rw [h6 _ hgi, h6 _ hi]
  · simp only [hi, ↓reduceIte]
    symm
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by decide) (by omega)))

theorem permWGo_lt : ∀ (p : List ℕ) (k w : ℕ), permWGo p k w < 2 ^ (k + p.length)
  | [], k, _ => by simp [permWGo]
  | idx :: rest, k, w => by
    have h1 : (((w >>> idx) &&& 1) <<< k) < 2 ^ (k + 1) := by
      rw [Nat.shiftLeft_eq]
      have hb : (w >>> idx) &&& 1 < 2 := by
        rw [show (1 : ℕ) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      have hmul : ((w >>> idx) &&& 1) * 2 ^ k < 2 * 2 ^ k := Nat.mul_lt_mul_of_pos_right hb (by positivity)
      have hpow : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      omega
    have h1' : (((w >>> idx) &&& 1) <<< k) < 2 ^ (k + (idx :: rest).length) :=
      lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by simp))
    have h2 : permWGo rest (k + 1) w < 2 ^ (k + (idx :: rest).length) := by
      have := permWGo_lt rest (k + 1) w
      have heq : k + 1 + rest.length = k + (idx :: rest).length := by simp; omega
      rwa [heq] at this
    exact Nat.or_lt_two_pow h1' h2

theorem permW_lt (p : List ℕ) (hp : p.length = 16) (w : ℕ) : permW p w < 65536 := by
  have h := permWGo_lt p 0 w
  simp [hp] at h
  exact h

theorem permW_comb (p : List ℕ) (hp : p.length = 16) (o : Fin 2) (a b : ℕ) :
    permW p (combM o a b) = combM o (permW p a) (permW p b) := by
  apply Nat.eq_of_testBit_eq; intro i
  fin_cases o <;> simp only [combM, Nat.testBit_land, Nat.testBit_lor, permW_testBit p hp] <;> split <;> simp

theorem canM_perm (p : List ℕ) (hp : p.length = 16) (hb : ∀ x ∈ p, x < 16) {f k : ℕ} {S : Finset ℕ}
    (hc : CanM f k S) : CanM (permW p f) k (S.image (permW p)) := by
  have hfree {T : Finset ℕ} {v : ℕ} (hv : freeM T v) : freeM (T.image (permW p)) (permW p v) := by
    rcases hv with rfl | rfl | h
    · exact Or.inl (permW_zero p hp)
    · exact Or.inr (Or.inl (permW_all p hp hb))
    · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ h))
  induction k generalizing S with
  | zero => exact hfree hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb', hh⟩ := hc
    refine ⟨o, permW p a, permW p b, hfree ha, hfree hb', ?_⟩
    have h' := ih hh
    rw [Finset.image_insert, permW_comb p hp] at h'
    exact h'

def treeHit (auts : List (List ℕ)) (nextTree : BinaryTree ℕ) (U : List ℕ) : Bool :=
  treeMem (packSet U) nextTree || auts.any (fun p => treeMem (packSet (U.map (permW p))) nextTree)

theorem treeHit_sound {auts : List (List ℕ)} {f k : ℕ} {nextTree : BinaryTree ℕ} {U : List ℕ}
    (hU : ∀ x ∈ U, x < 65536)
    (haut : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p f = f)
    (hh : treeHit auts nextTree U = true)
    (hc : CanM f k U.toFinset) :
    ∃ x, InTree x nextTree ∧ CanM f k (unpack x).toFinset := by
  simp only [treeHit, Bool.or_eq_true, List.any_eq_true] at hh
  rcases hh with h0 | ⟨p, hp, hm⟩
  · exact ⟨packSet U, treeMem_imp nextTree h0, monoCM_free (freeM_packSet hU) hc⟩
  · obtain ⟨hlen, hbd, hfix⟩ := haut p hp
    have hcp : CanM f k (U.map (permW p)).toFinset := by
      have h1 := canM_perm p hlen hbd hc
      have heq : (U.map (permW p)).toFinset = U.toFinset.image (permW p) := by
        ext y; simp
      rw [hfix, ← heq] at h1
      exact h1
    have hUp : ∀ y ∈ U.map (permW p), y < 65536 := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      exact permW_lt p hlen x
    exact ⟨packSet (U.map (permW p)), treeMem_imp nextTree hm, monoCM_free (freeM_packSet hUp) hcp⟩

def checkCuts (p1List : List ℕ) (p0Mask k : ℕ) (auts : List (List ℕ)) (nextTree : BinaryTree ℕ) (l : List ℕ) : Bool :=
  (cuts (k + 1) l).all fun U => !sepOk p1List p0Mask U || treeHit auts nextTree U

def verifyNode (p1List : List ℕ) (p0Mask k : ℕ) (auts : List (List ℕ)) (nextTree : BinaryTree ℕ) (packedS : ℕ) : Bool :=
  let S := unpack packedS
  checkCuts p1List p0Mask k auts nextTree S &&
  (valsNew S).all fun v => checkCuts p1List p0Mask k auts nextTree (v :: S)

theorem checkCuts_sound {f k : ℕ} {p1List : List ℕ} {p0Mask : ℕ} {auts : List (List ℕ)} {nextTree : BinaryTree ℕ} {l : List ℕ}
    (hl : ∀ x ∈ l, x < 65536)
    (hp1 : ∀ a ∈ p1List, f.testBit a = true)
    (hp0 : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ f.testBit b = false)
    (haut : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p f = f)
    (hchk : checkCuts p1List p0Mask k auts nextTree l = true)
    (hc : CanM f k l.toFinset) :
    ∃ x, InTree x nextTree ∧ CanM f k (unpack x).toFinset := by
  obtain ⟨T, hT, hn, ht⟩ := smallM hc
  obtain ⟨U, hU, hu⟩ := cutsSpec (k + 1) l T hT hn
  have hcU := monoCM hu ht
  have htest := List.all_eq_true.mp hchk U hU
  have hcov := coveredM hcU hp1 hp0
  simp only [hcov, Bool.not_true, Bool.false_or] at htest
  have hU_lt : ∀ x ∈ U, x < 65536 := fun x hx => hl x (cuts_mem_sub l (k + 1) U hU x hx)
  exact treeHit_sound hU_lt haut htest hcU

theorem advanceNode {f k : ℕ} {p1List : List ℕ} {p0Mask : ℕ} {auts : List (List ℕ)} {nextTree : BinaryTree ℕ} {packedS : ℕ}
    (hp1 : ∀ a ∈ p1List, f.testBit a = true)
    (hp0 : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ f.testBit b = false)
    (haut : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p f = f)
    (hv : verifyNode p1List p0Mask k auts nextTree packedS = true)
    (hc : CanM f (k + 1) (unpack packedS).toFinset) :
    ∃ x, InTree x nextTree ∧ CanM f k (unpack x).toFinset := by
  simp only [verifyNode, Bool.and_eq_true] at hv
  obtain ⟨o, a, b, ha, hb, hh⟩ := hc
  have hS_lt : ∀ x ∈ unpack packedS, x < 65536 := unpack_lt packedS
  rcases combM_case hS_lt ha hb with hfree | hnew
  · have hh' : CanM f k (unpack packedS).toFinset := by
      refine monoCM_free (fun x hx => ?_) hh
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hfree
      · exact Or.inr (Or.inr hx)
    exact checkCuts_sound hS_lt hp1 hp0 haut hv.1 hh'
  · have hv_lt : combM o a b < 65536 := by
      simp only [valsNew, List.mem_eraseDups, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hnew
      omega
    have hvl : ∀ x ∈ combM o a b :: unpack packedS, x < 65536 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv_lt
      · exact hS_lt x hx
    have hchk := List.all_eq_true.mp hv.2 (combM o a b) hnew
    exact checkCuts_sound hvl hp1 hp0 haut hchk (by simpa using hh)

abbrev targetNat : ℕ := 6126
abbrev p0Mask : ℕ := 59409
def p1List : List ℕ := [1, 2, 3, 5, 6, 7, 8, 9, 10, 12]
def inputs : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]
def auts : List (List ℕ) := [[0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13, 15], [4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15], [4, 6, 5, 7, 0, 2, 1, 3, 8, 10, 9, 11, 12, 14, 13, 15]]

def row1 : BinaryTree ℕ := BE
def row2 : BinaryTree ℕ := BN 175408182333951 (BN 130764876222208 (BL 112588801708543) (BL 157816264724991)) (BN 271502364577536 (BL 270918249025416) BE)
def row3LL : BinaryTree ℕ := BN 10342591603945902591 (BN 7378604826684821248 (BN 4919112399023181568 (BL 4919094222948667903) BE) (BN 9838243566751518464 (BL 9838225974783644159) BE)) (BN 10342646725001412863 (BN 10342629132830969856 (BL 10342629132814254335) BE) (BL 10342646725002330352))
def row3LR : BinaryTree ℕ := BN 17293935741792882432 (BN 11495550637423132912 (BN 11495550637422215423 (BL 11495513108284314111) BE) (BL 17293935157677330312)) (BN 17447582965537116040 (BN 17332215754509979392 (BL 17293980385098994175) BE) (BL 17447665722383012351))
def row3L : BinaryTree ℕ := BN 10991147479172321024 row3LL row3LR
def row3RL : BinaryTree ℕ := BN 17755036395535011584 (BN 17754897345927446783 (BN 17754897345918533870 (BL 17601231357512453888) BE) (BN 17755028698953617152 (BL 17754898368120750216) BE)) (BN 17755141287226314496 (BN 17755066228377849600 (BL 17755036396951048703) BE) (BL 17793177942751183103))
def row3RR : BinaryTree ℕ := BN 18369732518665457408 (BN 18062361844097421056 (BN 17908834836487802624 (BL 17908721734235066879) BE) (BL 18062520173771820800)) (BN 18413079665078898432 (BN 18374844295667913215 (BL 18369890848339857152) BE) (BL 18413124892500562431))
def row3R : BinaryTree ℕ := BN 17908676506813402880 row3RL row3RR
def row3 : BinaryTree ℕ := BN 17485863562369765120 row3L row3R
def row4LLL : BinaryTree ℕ := BN 644759130389605311840511 (BN 644757977468027690549503 (BN 644755517958519187837439 (BL 322377758980281813438208) (BL 644755517976111155711744)) (BN 644757977483420888006911 (BL 644757977469122923990784) (BL 644757977483420888924400))) (BN 677812083356198656606463 (BN 677812083338606469447935 (BL 644759130389665441382640) (BL 677812083338606486163456)) (BN 677814542848114971115535 (BL 677812083356198657523952) BE))
def row4LLR : BinaryTree ℕ := BN 753372406574102308978703 (BN 720315841194015028412671 (BN 677815695769692592406543 (BL 677814542848248367808752) (BL 720313381684433293086464)) (BN 753369947064520793981183 (BL 720315841194075157954800) (BL 753369947064520794898672))) (BN 1133375334492519317111039 (BN 1133372874983521688424192 (BL 1133372874982937572872072) (BL 1133375334492519308198126)) (BN 1133375372773116140847359 (BL 1133375334493541510414472) BE))
def row4LL : BinaryTree ℕ := BN 677814542848188238266623 row4LLL row4LLR
def row4LRL : BinaryTree ℕ := BN 1133378298517847682256640 (BN 1133378298517847667572991 (BN 1133378298517847666655487 (BL 1133378298480318528754175) (BL 1133378298517847667572976)) (BN 1133378298517847682252815 (BL 1133378298517847681339679) (BL 1133378298517847682253055))) (BN 1133378298555378522526207 (BN 1133378298517847682257183 (BL 1133378298517847682257169) (BL 1133378298517847952986623)) (BN 1133385172699728909897472 (BL 1133380253643035914473216) BE))
def row4LRR : BinaryTree ℕ := BN 1143450220782093081837823 (BN 1143449716341405407710976 (BN 1143444797228418234581247 (BL 1135884091686543807217919) (BL 1143444797229440427884680)) (BN 1143450220744563673206528 (BL 1143449716378934831943424) (BL 1143450220744563943936511))) (BN 1153514298244913975787775 (BN 1143452175869751905423104 (BL 1143450220782093082755312) (BL 1145953554422442724688127)) (BN 1153529248075230067232512 (BL 1153524098096467896372992) BE))
def row4LR : BinaryTree ℕ := BN 1135881632176962071891712 row4LRL row4LRR
def row4L : BinaryTree ℕ := BN 1133377794114689416761088 row4LL row4LR
def row4RLL : BinaryTree ℕ := BN 1163593560814624289263360 (BN 1163593560814564159721216 (BN 1163593560813662180999408 (BL 1163593560813602051457279) (BL 1163593560813662180999423)) (BN 1163593560814624253673727 (BL 1163593560814624253673487) (BL 1163593560814624288345856))) (BN 1163594065216820446494960 (BN 1163593560907425662308096 (BL 1163593560832366813843200) (BL 1163594065216760316952831)) (BN 1163594065310583913119984 (BL 1163594065310583912202495) BE))
def row4RLR : BinaryTree ℕ := BN 1173663023549561098469616 (BN 1163601016654138198396672 (BN 1163600939398641544593663 (BL 1163596020342008678711536) (BL 1163600939398701674135792)) (BN 1173660564039919233601280 (BL 1163601170339475482414848) (BL 1173663023549500968927487))) (BN 1173663023550523171143935 (BN 1173663023550463077191424 (BL 1173663023549561098469631) (BL 1173663023550523171143695)) (BN 1173663023550523206733568 (BL 1173663023550523205816064) BE))
def row4RL : BinaryTree ℕ := BN 1163596020341948549169407 row4RLL row4RLR
def row4RRL : BinaryTree ℕ := BN 1173673399843102560092400 (BN 1173665987574829328302320 (BN 1173665987537300189483519 (BL 1173665483171671077490432) (BL 1173665987574829327384831)) (BN 1173673092528662049132288 (BL 1173672938880854189346560) (BL 1173673399843042430550271))) (BN 1183745014792907464314624 (BN 1183734945813746384109823 (BL 1183732486304164648783616) (BL 1183734945813806513651952)) (BN 1183745322107347975274736 (BL 1183745322107287845732607) BE))
def row4RRR : BinaryTree ℕ := BN 1204213795760892345778416 (BN 1204213291357734094966528 (BN 1203889166635778676097279 (BL 1203878790342297344016624) (BL 1203889166635838805639408)) (BN 1204213795760892344860927 (BL 1204213795723363206959615) BE)) (BN 1206722552917387705979391 (BN 1206719588929588485423359 (BL 1206717129420006750097152) (BL 1206719588929648614965488)) (BN 1206722552954916844798192 (BL 1206722552954916843880703) BE))
def row4RR : BinaryTree ℕ := BN 1203878790342237214474495 row4RRL row4RRR
def row4R : BinaryTree ℕ := BN 1173663023568265731313408 row4RL row4RR
def row4 : BinaryTree ℕ := BN 1163584952462117036818568 row4L row4R
def row5LLLL : BinaryTree ℕ := BN 42254697626082419678522638591 (BN 42254697624929513494098804991 (BN 42254697624929499196134788864 (BL 42254697624929498100901347583) BE) (BL 42254697624929513494099722480)) (BN 42254858811349448902202884351 (BN 42254858811344662727851245583 (BL 42254697626082419738652180720) BE) (BL 42254858811353389551876833520))
def row5LLLR : BinaryTree ℕ := BN 44421092694831835159360176143 (BN 44421092693678913655006036223 (BN 44421092693678913581738885135 (BL 42254934369213173716778745871) BE) (BL 44421092693678913715135578352)) (BN 47206457782071019273512288511 (BL 44421253880098864383040421903) (BL 47206457782071019333641830640))
def row5LLL : BinaryTree ℕ := BN 42254858812353471316419936271 row5LLLL row5LLLR
def row5LLRL : BinaryTree ℕ := BN 74276885921301745382073499784 (BN 74276724734881796775735197832 (BN 74276724734881795753541894399 (BL 49372852850820434754349826063) BE) (BL 74276724734920076350365630719)) (BN 74277047115100284594652446975 (BL 74277047112640775012917120768) (BL 74277047115100284654781989104))
def row5LLRR : BinaryTree ℕ := BN 74277047115100285616890253056 (BN 74277047115100285616854663423 (BN 74277047115100285616854663183 (BL 74277047115100285556760710912) BE) (BL 74277047115100285616889335552)) (BN 74277080169206155100418015487 (BL 74277047115100303359414832896) (BL 74277080169206155100418932976))
def row5LLR : BinaryTree ℕ := BN 74277047115100284654781989119 row5LLRL row5LLRR
def row5LL : BinaryTree ℕ := BN 47206618968490968902051823631 row5LLL row5LLR
def row5LRLL : BinaryTree ℕ := BN 74277080169206155100433617169 (BN 74277080169206155100433613055 (BN 74277080169206155100433612815 (BL 74277080169206155100432699679) BE) (BL 74277080169206155100433616640)) (BN 74277080171665664681933996047 (BN 74277080171665664681933013007 (BL 74277080169206155100433617183) BE) (BL 74277080171665664682168942847))
def row5LRLR : BinaryTree ℕ := BN 74277080174125249323124003327 (BN 74277080171665683446915727615 (BN 74277080171665664742333153520 (BL 74277080171665664742298484976) BE) (BL 74277080171665683446916645104)) (BN 74277080174125286852262822128 (BL 74277080174125286852261904639) (BL 74277208300290491086979141376))
def row5LRL : BinaryTree ℕ := BN 74277080171665664742062555151 row5LRLL row5LRLR
def row5LRRL : BinaryTree ℕ := BN 74936798231161616837401051272 (BN 74277530678049432876968050928 (BN 74277530678049432816838508799 (BL 74277208302750000728844009712) BE) (BL 74441138646349385321293021439)) (BN 74937120610150343837673849072 (BL 74937120610150343777544306943) (BL 74937120610150343837673849087))
def row5LRRR : BinaryTree ℕ := BN 74937120610150362542306692864 (BN 74937120610150344799781195520 (BN 74937120610150344799746523391 (BL 74937120610150344799746523151) BE) (BL 74937120610150344799782113024)) (BN 74937120612609872184171561200 (BL 74937120612609872124042019071) (BL 74937153666715723865060802815))
def row5LRR : BinaryTree ℕ := BN 74937120610150344739652570880 row5LRRL row5LRRR
def row5LR : BinaryTree ℕ := BN 74277208302750000668714467583 row5LRL row5LRR
def row5L : BinaryTree ℕ := BN 74277080169206155100418932991 row5LL row5LR
def row5RLLL : BinaryTree ℕ := BN 74937281797800059911735869680 (BN 74937153669175252211322585103 (BN 74937153666715742629808505072 (BL 74937153666715742629807587583) BE) (BL 74937281797800059851606327551)) (BN 75597355292850119094627729648 (BN 75597355292850119034498187519 (BL 74937609232426481183329554176) BE) (BL 75597692801858276663947690239))
def row5RLLR : BinaryTree ℕ := BN 76257267602709990489825739007 (BN 76257267601484164693977202703 (BN 76257267601480224044304236559 (BL 76257267601480224044303253519) BE) (BL 76257267601484166966250832112)) (BN 76257267607629047182821163263 (BL 76257267602709990549955281136) (BL 76257267607629047242950705392))
def row5RLL : BinaryTree ℕ := BN 75597692801858276724077232368 row5RLLL row5RLLR
def row5RLRL : BinaryTree ℕ := BN 76257756227445600008051622128 (BN 76257751164429372266489315343 (BN 76257428789129940118365274127 (BL 76257300664194427270101729295) BE) (BL 76257756227445599947922079999)) (BN 76257766299367864253466804464 (BL 76257766299367864193337262335) (BL 76917018724920145871091269887))
def row5RLRR : BinaryTree ℕ := BN 76917018724920146893328158464 (BN 76917018724920146893293486095 (BN 76917018724920146833199533824 (BL 76917018724920145931220812031) BE) (BL 76917018724920146893293486335)) (BN 76917179911340095499630805007 (BL 76917018724920146893329075968) (BL 76917179911340095499631788047))
def row5RLR : BinaryTree ℕ := BN 76917018724920145931220812016 row5RLRL row5RLRR
def row5RL : BinaryTree ℕ := BN 76257300658045604131819749391 row5RLL row5RLR
def row5RRLL : BinaryTree ℕ := BN 76917341105138634712210735359 (BN 76917179912569862005282832624 (BN 76917179912569861945153290495 (BL 76917179911344038421578383600) BE) (BL 76917341102679125130475409152)) (BN 76917374159244505217976303871 (BL 76917341105138634772340277488) (BL 76917374159244505217977221360))
def row5RRLR : BinaryTree ℕ := BN 76917839791958395089860952304 (BN 76917829722495659190943482096 (BN 76917829722495659130813939967 (BL 76917829720036149549078613760) BE) (BL 76917839791958395029731410175)) (BN 77577092222429733400480841983 (BL 76917859932113628728541577231) (BL 77577092222429733460610384112))
def row5RRL : BinaryTree ℕ := BN 76917374161704014799491301391 row5RRLL row5RRLR
def row5RRRL : BinaryTree ℕ := BN 78898080424642391316710293519 (BN 77577933429623216257931149327 (BN 77577913289467982619250524400 (BL 77577913289467982559120982271) BE) (BL 78897400403868858087799521295)) (BN 78919322262420460625524162815 (BL 78919322259960951043788836608) (BL 78919322262420460685653704944))
def row5RRRR : BinaryTree ℕ := BN 79083574980089510980704272399 (BN 79083413793669561352164737279 (BN 78919355318985840712804728847 (BL 78919355316526331131290648816) BE) (BL 79083413793669561412294279408)) (BN 79083769227993920699050688752 (BL 79083769227993920699049771263) (BL 79083769230453430280564768783))
def row5RRR : BinaryTree ℕ := BN 78919355316526331131289731327 row5RRRL row5RRRR
def row5RR : BinaryTree ℕ := BN 77577253408849683029020377103 row5RRL row5RRR
def row5R : BinaryTree ℕ := BN 76917179911344036149304754191 row5RL row5RR
def row5 : BinaryTree ℕ := BN 74937153666715723925190344944 row5L row5R
def row6LLL : BinaryTree ℕ := BN 2769203863622937456051659641716751 (BN 2769203863547379596267494739804400 (BN 2769203863547379592326845065855231 (BL 2769203863547379587540670714216463) BE) (BL 2769203863547380596349259282907151)) (BN 3093722417205806319108901338873871 (BN 2911180730772941285294475588927503 (BL 2769214427060597483254768227844111) BE) (BL 4867799432225213366503537475780744))
def row6LLR : BinaryTree ℕ := BN 4867820559574025831246536426651903 (BN 4867820559574025831246476332699392 (BN 4867820559574025831245574353977599 (BL 4867820559574025831245574353977584) BE) (BL 4867820559574025831246536426651663)) (BN 4867820559735212251195142763970575 (BN 4867820559574025831246536462241536 (BL 4867820559574025831246536461324032) BE) (BL 4867820559735212251195142764953615))
def row6LL : BinaryTree ℕ := BN 4867820559574025831245514224435455 row6LLL row6LLR
def row6LRL : BinaryTree ℕ := BN 4867822725969094580660995062956047 (BN 4867820559735213480961648415998192 (BN 4867820559735213480961588286456063 (BL 4867820559735212255138064711549168) BE) (BL 4867822725969094580660995061973007)) (BN 4867822725969094580661055427444976 (BN 4867822725969094580661055191515151 (BL 4867822725969094580660995297902847) BE) (BL 4867822725969094580661055462113520))
def row6LRR : BinaryTree ℕ := BN 4867831123167837623875242807001343 (BN 4867822726291472339640254667358448 (BN 4867822726291472339640254666440959 (BL 4867822726130282230377069123993615) BE) (BL 4867822726291474799149836181438479)) (BN 4867831123329024043824871346536463 (BL 4867831123167837623875302936543472) (BL 4867852250516647629084328511668239))
def row6LR : BinaryTree ℕ := BN 4867822726130281000610623837437967 row6LRL row6LRR
def row6L : BinaryTree ℕ := BN 4867820559735212255135792437919759 row6LL row6LR
def row6RLL : BinaryTree ℕ := BN 4911079136306814159571649350861040 (BN 4911079136306812933748065646412016 (BN 4911079136306812933745793372782607 (BL 4911079136306812929805143699816463) BE) (BL 4911079136306814159571589221318911)) (BN 4911081302701882908987070058856463 (BN 4911081302701881679220624772300815 (BL 4911079136468000579521217760854031) BE) (BL 4911089699900624722434872281399311))
def row6RLR : BinaryTree ℕ := BN 4997596289933577236173367754620943 (BN 4954370395462584019448475826520079 (BN 4954348276472225401044873216262159 (BL 4911111158656301870829723589804272) BE) (BL 4997596289611201936741219630579727)) (BN 5040833739156366679807837462331407 (BN 4997628972195372347774550823403535 (BL 4997628312121874838187021433831439) BE) (BL 5040833739156366679807837463314447))
def row6RL : BinaryTree ℕ := BN 4911111158656301870829663460262143 row6RLL row6RLR
def row6RRL : BinaryTree ℕ := BN 5040854866666365564499442751504399 (BN 5040854866505179144549814211969279 (BN 5040844302750178472437566044897295 (BL 5040833739156366683750759409910000) BE) (BL 5040854866505179144549874341511408)) (BN 5040886888532289096847453958701296 (BN 5040886888532289096847393829159167 (BL 5040857032900247893965295049506831) BE) (BL 5040886888693475516797022368694287))
def row6RRR : BinaryTree ℕ := BN 5172056703789987307554351533260815 (BN 5172056703628800887604722993725695 (BN 5084146125338573704994552693129231 (BL 5084092315889155008133912459214863) BE) (BL 5172056703628800887604783123267824)) (BN 5182810606381928372775468221333519 (BL 5172058870023869637020203831263247) (BL 5182833900125809586932925808508943))
def row6RR : BinaryTree ℕ := BN 5040887548605785376668477696245775 row6RRL row6RRR
def row6R : BinaryTree ℕ := BN 5040833739156366683748487136280591 row6RL row6RR
def row6 : BinaryTree ℕ := BN 4911079136306812929805143698833423 row6L row6R
def row7 : BinaryTree ℕ := BN 319017630190237931250663729819873705999 (BN 319017488192243356876509960862274945039 (BN 319017488192243356876506020212600995855 (BL 181482544401441068962732118235887435791) (BL 319017488192243356876506020212601978895)) (BN 319017488202806950688298649941183561743 (BL 319017488192243356876509963134548574448) (BL 319017630169110582438198987843359997967))) (BN 330357464531283420417216624195617685519 (BN 321852482277003372761683671208355168271 (BL 319018180487927406518287912599639031823) (BL 321854580893699399406692824531738820623)) (BN 338955908129017094970063126116806164495 (BL 330359563126852098250990801987774185487) BE))
def row8 : BinaryTree ℕ := BL 319017488192243356876506020212600995855

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit : checkCuts p1List p0Mask 8 auts row8 inputs = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row2 : checkTree (verifyNode p1List p0Mask 1 auts row1) row2 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row3LL : checkTree (verifyNode p1List p0Mask 2 auts row2) row3LL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row3LR : checkTree (verifyNode p1List p0Mask 2 auts row2) row3LR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row3LV : (verifyNode p1List p0Mask 2 auts row2) 10991147479172321024 = true := by decide +kernel
theorem chk_row3L : checkTree (verifyNode p1List p0Mask 2 auts row2) row3L = true := checkTree_node chk_row3LV chk_row3LL chk_row3LR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row3RL : checkTree (verifyNode p1List p0Mask 2 auts row2) row3RL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row3RR : checkTree (verifyNode p1List p0Mask 2 auts row2) row3RR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row3RV : (verifyNode p1List p0Mask 2 auts row2) 17908676506813402880 = true := by decide +kernel
theorem chk_row3R : checkTree (verifyNode p1List p0Mask 2 auts row2) row3R = true := checkTree_node chk_row3RV chk_row3RL chk_row3RR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row3V : (verifyNode p1List p0Mask 2 auts row2) 17485863562369765120 = true := by decide +kernel
theorem chk_row3 : checkTree (verifyNode p1List p0Mask 2 auts row2) row3 = true := checkTree_node chk_row3V chk_row3L chk_row3R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row4LLL : checkTree (verifyNode p1List p0Mask 3 auts row3) row4LLL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row4LLR : checkTree (verifyNode p1List p0Mask 3 auts row3) row4LLR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row4LLV : (verifyNode p1List p0Mask 3 auts row3) 677814542848188238266623 = true := by decide +kernel
theorem chk_row4LL : checkTree (verifyNode p1List p0Mask 3 auts row3) row4LL = true := checkTree_node chk_row4LLV chk_row4LLL chk_row4LLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row4LRL : checkTree (verifyNode p1List p0Mask 3 auts row3) row4LRL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row4LRR : checkTree (verifyNode p1List p0Mask 3 auts row3) row4LRR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row4LRV : (verifyNode p1List p0Mask 3 auts row3) 1135881632176962071891712 = true := by decide +kernel
theorem chk_row4LR : checkTree (verifyNode p1List p0Mask 3 auts row3) row4LR = true := checkTree_node chk_row4LRV chk_row4LRL chk_row4LRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row4LV : (verifyNode p1List p0Mask 3 auts row3) 1133377794114689416761088 = true := by decide +kernel
theorem chk_row4L : checkTree (verifyNode p1List p0Mask 3 auts row3) row4L = true := checkTree_node chk_row4LV chk_row4LL chk_row4LR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row4RLL : checkTree (verifyNode p1List p0Mask 3 auts row3) row4RLL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row4RLR : checkTree (verifyNode p1List p0Mask 3 auts row3) row4RLR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row4RLV : (verifyNode p1List p0Mask 3 auts row3) 1163596020341948549169407 = true := by decide +kernel
theorem chk_row4RL : checkTree (verifyNode p1List p0Mask 3 auts row3) row4RL = true := checkTree_node chk_row4RLV chk_row4RLL chk_row4RLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row4RRL : checkTree (verifyNode p1List p0Mask 3 auts row3) row4RRL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row4RRR : checkTree (verifyNode p1List p0Mask 3 auts row3) row4RRR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row4RRV : (verifyNode p1List p0Mask 3 auts row3) 1203878790342237214474495 = true := by decide +kernel
theorem chk_row4RR : checkTree (verifyNode p1List p0Mask 3 auts row3) row4RR = true := checkTree_node chk_row4RRV chk_row4RRL chk_row4RRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row4RV : (verifyNode p1List p0Mask 3 auts row3) 1173663023568265731313408 = true := by decide +kernel
theorem chk_row4R : checkTree (verifyNode p1List p0Mask 3 auts row3) row4R = true := checkTree_node chk_row4RV chk_row4RL chk_row4RR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row4V : (verifyNode p1List p0Mask 3 auts row3) 1163584952462117036818568 = true := by decide +kernel
theorem chk_row4 : checkTree (verifyNode p1List p0Mask 3 auts row3) row4 = true := checkTree_node chk_row4V chk_row4L chk_row4R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5LLLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LLLL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5LLLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LLLR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5LLLV : (verifyNode p1List p0Mask 4 auts row4) 42254858812353471316419936271 = true := by decide +kernel
theorem chk_row5LLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LLL = true := checkTree_node chk_row5LLLV chk_row5LLLL chk_row5LLLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5LLRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LLRL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5LLRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LLRR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5LLRV : (verifyNode p1List p0Mask 4 auts row4) 74277047115100284654781989119 = true := by decide +kernel
theorem chk_row5LLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LLR = true := checkTree_node chk_row5LLRV chk_row5LLRL chk_row5LLRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5LLV : (verifyNode p1List p0Mask 4 auts row4) 47206618968490968902051823631 = true := by decide +kernel
theorem chk_row5LL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LL = true := checkTree_node chk_row5LLV chk_row5LLL chk_row5LLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5LRLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LRLL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5LRLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LRLR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5LRLV : (verifyNode p1List p0Mask 4 auts row4) 74277080171665664742062555151 = true := by decide +kernel
theorem chk_row5LRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LRL = true := checkTree_node chk_row5LRLV chk_row5LRLL chk_row5LRLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5LRRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LRRL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5LRRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LRRR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5LRRV : (verifyNode p1List p0Mask 4 auts row4) 74937120610150344739652570880 = true := by decide +kernel
theorem chk_row5LRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LRR = true := checkTree_node chk_row5LRRV chk_row5LRRL chk_row5LRRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5LRV : (verifyNode p1List p0Mask 4 auts row4) 74277208302750000668714467583 = true := by decide +kernel
theorem chk_row5LR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5LR = true := checkTree_node chk_row5LRV chk_row5LRL chk_row5LRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5LV : (verifyNode p1List p0Mask 4 auts row4) 74277080169206155100418932991 = true := by decide +kernel
theorem chk_row5L : checkTree (verifyNode p1List p0Mask 4 auts row4) row5L = true := checkTree_node chk_row5LV chk_row5LL chk_row5LR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5RLLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RLLL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5RLLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RLLR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5RLLV : (verifyNode p1List p0Mask 4 auts row4) 75597692801858276724077232368 = true := by decide +kernel
theorem chk_row5RLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RLL = true := checkTree_node chk_row5RLLV chk_row5RLLL chk_row5RLLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5RLRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RLRL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5RLRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RLRR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5RLRV : (verifyNode p1List p0Mask 4 auts row4) 76917018724920145931220812016 = true := by decide +kernel
theorem chk_row5RLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RLR = true := checkTree_node chk_row5RLRV chk_row5RLRL chk_row5RLRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5RLV : (verifyNode p1List p0Mask 4 auts row4) 76257300658045604131819749391 = true := by decide +kernel
theorem chk_row5RL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RL = true := checkTree_node chk_row5RLV chk_row5RLL chk_row5RLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5RRLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RRLL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5RRLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RRLR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5RRLV : (verifyNode p1List p0Mask 4 auts row4) 76917374161704014799491301391 = true := by decide +kernel
theorem chk_row5RRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RRL = true := checkTree_node chk_row5RRLV chk_row5RRLL chk_row5RRLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5RRRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RRRL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row5RRRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RRRR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5RRRV : (verifyNode p1List p0Mask 4 auts row4) 78919355316526331131289731327 = true := by decide +kernel
theorem chk_row5RRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RRR = true := checkTree_node chk_row5RRRV chk_row5RRRL chk_row5RRRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5RRV : (verifyNode p1List p0Mask 4 auts row4) 77577253408849683029020377103 = true := by decide +kernel
theorem chk_row5RR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5RR = true := checkTree_node chk_row5RRV chk_row5RRL chk_row5RRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5RV : (verifyNode p1List p0Mask 4 auts row4) 76917179911344036149304754191 = true := by decide +kernel
theorem chk_row5R : checkTree (verifyNode p1List p0Mask 4 auts row4) row5R = true := checkTree_node chk_row5RV chk_row5RL chk_row5RR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row5V : (verifyNode p1List p0Mask 4 auts row4) 74937153666715723925190344944 = true := by decide +kernel
theorem chk_row5 : checkTree (verifyNode p1List p0Mask 4 auts row4) row5 = true := checkTree_node chk_row5V chk_row5L chk_row5R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row6LLL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6LLL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row6LLR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6LLR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row6LLV : (verifyNode p1List p0Mask 5 auts row5) 4867820559574025831245514224435455 = true := by decide +kernel
theorem chk_row6LL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6LL = true := checkTree_node chk_row6LLV chk_row6LLL chk_row6LLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row6LRL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6LRL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row6LRR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6LRR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row6LRV : (verifyNode p1List p0Mask 5 auts row5) 4867822726130281000610623837437967 = true := by decide +kernel
theorem chk_row6LR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6LR = true := checkTree_node chk_row6LRV chk_row6LRL chk_row6LRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row6LV : (verifyNode p1List p0Mask 5 auts row5) 4867820559735212255135792437919759 = true := by decide +kernel
theorem chk_row6L : checkTree (verifyNode p1List p0Mask 5 auts row5) row6L = true := checkTree_node chk_row6LV chk_row6LL chk_row6LR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row6RLL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6RLL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row6RLR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6RLR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row6RLV : (verifyNode p1List p0Mask 5 auts row5) 4911111158656301870829663460262143 = true := by decide +kernel
theorem chk_row6RL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6RL = true := checkTree_node chk_row6RLV chk_row6RLL chk_row6RLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row6RRL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6RRL = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row6RRR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6RRR = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row6RRV : (verifyNode p1List p0Mask 5 auts row5) 5040887548605785376668477696245775 = true := by decide +kernel
theorem chk_row6RR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6RR = true := checkTree_node chk_row6RRV chk_row6RRL chk_row6RRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row6RV : (verifyNode p1List p0Mask 5 auts row5) 5040833739156366683748487136280591 = true := by decide +kernel
theorem chk_row6R : checkTree (verifyNode p1List p0Mask 5 auts row5) row6R = true := checkTree_node chk_row6RV chk_row6RL chk_row6RR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk_row6V : (verifyNode p1List p0Mask 5 auts row5) 4911079136306812929805143698833423 = true := by decide +kernel
theorem chk_row6 : checkTree (verifyNode p1List p0Mask 5 auts row5) row6 = true := checkTree_node chk_row6V chk_row6L chk_row6R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row7 : checkTree (verifyNode p1List p0Mask 6 auts row6) row7 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk_row8 : checkTree (verifyNode p1List p0Mask 7 auts row7) row8 = true := by decide +kernel

theorem hp1_proof : ∀ a ∈ p1List, targetNat.testBit a = true := by decide +kernel
theorem hp0_fin : ∀ b : Fin 16, p0Mask.testBit b.val = true → targetNat.testBit b.val = false := by decide +kernel
theorem hp0_proof : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ targetNat.testBit b = false := by
  intro b hb
  by_cases h16 : b < 16
  · exact ⟨h16, hp0_fin ⟨b, h16⟩ hb⟩
  · have hf : p0Mask.testBit b = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : p0Mask < 2 ^ 16) (Nat.pow_le_pow_right (by decide) (by omega)))
    exact absurd hb (by simp [hf])
theorem haut_proof : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p targetNat = targetNat := by decide +kernel
theorem inputs_lt : ∀ t ∈ inputs, t < 65536 := by decide
theorem targetNat_lt : targetNat < 2 ^ 16 := by decide

theorem excluded (hc : CanM targetNat 8 inputs.toFinset) : False := by
  obtain ⟨x8, hx8, c8⟩ := checkCuts_sound inputs_lt hp1_proof hp0_proof haut_proof chkInit hc
  obtain ⟨x7, hx7, c7⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row8 chk_row8 x8 hx8) c8
  obtain ⟨x6, hx6, c6⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row7 chk_row7 x7 hx7) c7
  obtain ⟨x5, hx5, c5⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row6 chk_row6 x6 hx6) c6
  obtain ⟨x4, hx4, c4⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row5 chk_row5 x5 hx5) c5
  obtain ⟨x3, hx3, c3⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row4 chk_row4 x4 hx4) c4
  obtain ⟨x2, hx2, c2⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row3 chk_row3 x3 hx3) c3
  obtain ⟨x1, hx1, c1⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row2 chk_row2 x2 hx2) c2
  exact hx1

theorem oneEach_map (p : Fin 16) :
    oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4) =
    inputs.map (fun t => t.testBit p.val) := by
  revert p; decide

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (6126 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  rintro ⟨C, hC, hs, hrep⟩
  have hok : ∀ g ∈ C.gates, GOkM g := hC
  let out := (tabsM inputs C.gates).getD C.output 0
  have obs (p : Fin 16) : out.testBit p.val = targetNat.testBit p.val := by
    have hval := hrep ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩
    unfold Circuit.eval Circuit.wires at hval
    rw [oneEach_map p, wires_tabsM p C.gates inputs hok, getD_map_testBitM] at hval
    dsimp only at hval
    have he : 4 * (p.val / 4) + p.val % 4 = p.val := Nat.div_add_mod p.val 4
    rw [he] at hval
    exact hval
  have hout_eq : out = targetNat := by
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p < 16
    · exact obs ⟨p, hp⟩
    · have h2 : 2 ^ 16 ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
      have hT : targetNat.testBit p = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le targetNat_lt h2)
      have hI : ∀ v ∈ inputs, v.testBit p = false := fun v hv => Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (inputs_lt v hv) h2)
      have hall := tabsM_bit_false p (by omega) C.gates inputs hI
      have hout_f : out.testBit p = false := by
        dsimp [out]
        rw [List.getD_eq_getElem?_getD]
        cases hget : (tabsM inputs C.gates)[C.output]? with
        | none => simp
        | some v => exact hall v (List.mem_of_getElem? hget)
      rw [hout_f, hT]
  have hc := fromTabsM out C.gates inputs hok (getWireM _ C.output)
  rw [hout_eq] at hc
  have pad {k j : ℕ} (hj : k ≤ j) (ha : CanM targetNat k inputs.toFinset) : CanM targetNat j inputs.toFinset := by
    induction hj with
    | refl => exact ha
    | step _ ih => exact stepUpM ih
  change C.gates.length ≤ _ at hs
  exact excluded (pad hs hc)

end PEqualNP.Outside.L_meta_6380_aux

theorem PEqualNP.Outside.L_meta_6380 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (6126 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (6126 : ℕ).testBit (4 * u.val + v.val)) 8 :=
  ⟨PEqualNP.Outside.L_meta_6380_aux.upper, PEqualNP.Outside.L_meta_6380_aux.lower⟩
