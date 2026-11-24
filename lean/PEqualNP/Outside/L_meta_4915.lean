import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4915

open PEqualNP.CircuitLowerBounds PEqualNP.BicliqueBlockCost PEqualNP.SharedBlockCost

lemma getD_lt {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

lemma getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma getD_snoc {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  split_ifs with h1 h2
  · rw [getD_lt _ _ _ (by simp; omega), getD_lt _ _ _ h1]
    simp [h1]
  · subst h2
    rw [getD_lt _ _ _ (by simp)]
    simp
  · rw [getD_ge _ _ _ (by simp; omega)]

def stepSets {n : ℕ} (acc : List (Finset (Fin n))) (g : Gate) : List (Finset (Fin n)) :=
  acc ++ [(g.inputs.map (fun i => acc.getD i ∅)).foldr (· ∪ ·) ∅]

def sets (n : ℕ) (gs : List Gate) : List (Finset (Fin n)) :=
  gs.foldl stepSets (List.ofFn (fun i : Fin n => ({i} : Finset (Fin n))))

def wv (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def allOr (gs : List Gate) : Prop := ∀ g ∈ gs, g.op = GateOp.or

def OK (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), isOrOp (gs[j]'h).op = true ∧
    (gs[j]'h).inputs.length = 2 ∧ ∀ i ∈ (gs[j]'h).inputs, i < n + j

lemma sets_snoc (n : ℕ) (gs : List Gate) (g : Gate) :
    sets n (gs ++ [g]) = stepSets (sets n gs) g := by
  simp only [sets, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma wv_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wv (gs ++ [g]) x = wv gs x ++ [g.op.eval (g.inputs.map fun i => (wv gs x).getD i false)] := by
  simp only [wv, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma length_sets (n : ℕ) (gs : List Gate) : (sets n gs).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [sets]
  | append_singleton gs g ih =>
    rw [sets_snoc]
    unfold stepSets
    simp only [List.length_append, List.length_singleton, ih]
    omega

lemma length_wv (gs : List Gate) (x : List Bool) : (wv gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wv]
  | append_singleton gs g ih =>
    rw [wv_snoc]
    simp only [List.length_append, List.length_singleton, ih]
    omega

lemma any_map_iff (l : List ℕ) (f : ℕ → Bool) : (l.map f).any id = true ↔ ∃ a ∈ l, f a = true := by
  simp

lemma mem_foldr {n : ℕ} (l : List ℕ) (h : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map h).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ h a := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma sem (n : ℕ) (gs : List Gate) (hor : allOr gs) (y : Fin n → Bool) (w : ℕ) :
    (wv gs (List.ofFn y)).getD w false = true ↔ ∃ i ∈ (sets n gs).getD w ∅, y i = true := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    by_cases hw : w < n
    · rw [getD_lt _ _ _ (by simpa [wv] using hw), getD_lt _ _ _ (by simpa [sets] using hw)]
      simp [wv, sets]
    · rw [getD_ge _ _ _ (by simp [wv]; omega), getD_ge _ _ _ (by simp [sets]; omega)]
      simp
  | append_singleton gs g ih =>
    have hor0 : allOr gs := fun g' hg' => hor g' (List.mem_append_left _ hg')
    have hg : g.op = GateOp.or := hor g (by simp)
    rw [wv_snoc, sets_snoc]
    unfold stepSets
    rw [getD_snoc, getD_snoc, length_wv, length_sets, List.length_ofFn]
    split_ifs with h1 h2
    · exact ih hor0 w
    · rw [hg]
      simp only [GateOp.eval]
      constructor
      · intro hv
        rw [any_map_iff] at hv
        obtain ⟨a, ha, hva⟩ := hv
        obtain ⟨i, hi, hyi⟩ := (ih hor0 a).1 hva
        exact ⟨i, (mem_foldr _ _ _).2 ⟨a, ha, hi⟩, hyi⟩
      · rintro ⟨i, hi, hyi⟩
        rw [mem_foldr] at hi
        obtain ⟨a, ha, hia⟩ := hi
        rw [any_map_iff]
        exact ⟨a, ha, (ih hor0 a).2 ⟨i, hia, hyi⟩⟩
    · simp

lemma computes_set {n : ℕ} (C : Circuit) (hor : allOr C.gates) (w : ℕ) (s : Finset (Fin n))
    (h : ComputesOr n C w s) : (sets n C.gates).getD w ∅ = s := by
  ext i
  have h1 := h.2 (fun j => decide (j = i))
  have h2 := sem n C.gates hor (fun j => decide (j = i)) w
  have h3 : (∃ j ∈ (sets n C.gates).getD w ∅, decide (j = i) = true) ↔
      ∃ j ∈ s, decide (j = i) = true := h2.symm.trans h1
  simpa using h3

lemma isOr_eq (op : GateOp) (h : isOrOp op = true) : op = GateOp.or := by
  cases op <;> first | rfl | simp [isOrOp] at h

lemma ok_allOr {n : ℕ} {gs : List Gate} (h : OK n gs) : allOr gs := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  exact isOr_eq _ (h j hj).1

lemma OK_snoc {n : ℕ} {gs : List Gate} {g : Gate} (h : OK n (gs ++ [g])) :
    OK n gs ∧ isOrOp g.op = true ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n + gs.length := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have h1 := h j (by simp; omega)
    have e : (gs ++ [g])[j]'(by simp; omega) = gs[j] := by simp [hj]
    rw [e] at h1
    exact h1
  · have h1 := h gs.length (by simp)
    have e : (gs ++ [g])[gs.length]'(by simp) = g := by simp
    rw [e] at h1
    exact h1

lemma two (l : List ℕ) (h : l.length = 2) : ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp at h
  exact ⟨a, b, rfl⟩

def un (n : ℕ) (gs : List Gate) (ws : Finset ℕ) : Finset (Fin n) :=
  ws.biUnion (fun w => (sets n gs).getD w ∅)

def Gu (n : ℕ) (gs : List Gate) (U : Finset (Fin n)) : Finset ℕ :=
  (Finset.range gs.length).filter
    (fun j => (sets n gs).getD (n + j) ∅ ⊆ U ∧ 2 ≤ ((sets n gs).getD (n + j) ∅).card)

lemma count_main (n : ℕ) (U : Finset (Fin n)) : ∀ (gs : List Gate), OK n gs →
    ∀ ws : Finset ℕ, un n gs ws ⊆ U → (un n gs ws).card ≤ (Gu n gs U).card + ws.card := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ ws _
    have h1 : ∀ w, ((sets n []).getD w ∅).card ≤ 1 := by
      intro w
      by_cases hw : w < n
      · rw [getD_lt _ _ _ (by simpa [sets] using hw)]
        simp [sets]
      · rw [getD_ge _ _ _ (by simp [sets]; omega)]
        simp
    calc (un n [] ws).card ≤ ∑ w ∈ ws, ((sets n []).getD w ∅).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ ws, 1 := Finset.sum_le_sum (fun w _ => h1 w)
      _ = ws.card := by simp
      _ ≤ (Gu n [] U).card + ws.card := Nat.le_add_left _ _
  | append_singleton gs g ih =>
    intro hok ws hsub
    obtain ⟨hok0, _, hglen, hgin⟩ := OK_snoc hok
    obtain ⟨a, b, hab⟩ := two _ hglen
    have hTg : (sets n (gs ++ [g])).getD (n + gs.length) ∅ =
        (sets n gs).getD a ∅ ∪ (sets n gs).getD b ∅ := by
      rw [sets_snoc]
      unfold stepSets
      rw [getD_snoc, length_sets]
      simp [hab]
    have hold : ∀ w, w ≠ n + gs.length → (sets n (gs ++ [g])).getD w ∅ = (sets n gs).getD w ∅ := by
      intro w hw
      rw [sets_snoc]
      unfold stepSets
      rw [getD_snoc, length_sets]
      split_ifs <;> first | rfl | (exfalso; omega) | rw [getD_ge _ _ _ (by rw [length_sets]; omega)]
    have hA : ((Finset.range gs.length).filter (fun j => (sets n (gs ++ [g])).getD (n + j) ∅ ⊆ U ∧
        2 ≤ ((sets n (gs ++ [g])).getD (n + j) ∅).card)).card = (Gu n gs U).card := by
      unfold Gu
      congr 1
      apply Finset.filter_congr
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hold (n + j) (by omega)]
    have hsubA : (Finset.range gs.length).filter (fun j => (sets n (gs ++ [g])).getD (n + j) ∅ ⊆ U ∧
        2 ≤ ((sets n (gs ++ [g])).getD (n + j) ∅).card) ⊆ Gu n (gs ++ [g]) U := by
      intro j hj
      unfold Gu
      rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
      obtain ⟨hj1, hj2⟩ := hj
      refine ⟨?_, hj2⟩
      rw [List.length_append, List.length_singleton]
      omega
    have hcnt1 : (Gu n gs U).card ≤ (Gu n (gs ++ [g]) U).card := by
      rw [← hA]
      exact Finset.card_le_card hsubA
    have hcnt2 : ((sets n gs).getD a ∅ ∪ (sets n gs).getD b ∅) ⊆ U →
        2 ≤ ((sets n gs).getD a ∅ ∪ (sets n gs).getD b ∅).card →
        (Gu n gs U).card + 1 ≤ (Gu n (gs ++ [g]) U).card := by
      intro hc1 hc2
      rw [← hA]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsubA]
      refine ⟨gs.length, ?_, ?_⟩
      · unfold Gu
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by simp, ?_⟩
        show (sets n (gs ++ [g])).getD (n + gs.length) ∅ ⊆ U ∧
          2 ≤ ((sets n (gs ++ [g])).getD (n + gs.length) ∅).card
        rw [hTg]
        exact ⟨hc1, hc2⟩
      · intro hmem
        rw [Finset.mem_filter, Finset.mem_range] at hmem
        exact lt_irrefl _ hmem.1
    by_cases hm : n + gs.length ∈ ws
    · have hTU : ((sets n gs).getD a ∅ ∪ (sets n gs).getD b ∅) ⊆ U := by
        intro i hi
        apply hsub
        unfold un
        rw [Finset.mem_biUnion]
        exact ⟨_, hm, by rw [hTg]; exact hi⟩
      have hpos : 0 < ws.card := Finset.card_pos.2 ⟨_, hm⟩
      by_cases h2 : 2 ≤ ((sets n gs).getD a ∅ ∪ (sets n gs).getD b ∅).card
      · have hs1 : un n (gs ++ [g]) ws ⊆ un n gs (ws.erase (n + gs.length) ∪ {a, b}) := by
          intro i hi
          unfold un at hi ⊢
          rw [Finset.mem_biUnion] at hi ⊢
          obtain ⟨w, hw, hiw⟩ := hi
          by_cases hwm : w = n + gs.length
          · rw [hwm, hTg, Finset.mem_union] at hiw
            rcases hiw with h | h
            · exact ⟨a, by simp, h⟩
            · exact ⟨b, by simp, h⟩
          · rw [hold w hwm] at hiw
            exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwm, hw⟩), hiw⟩
        have hs2 : un n gs (ws.erase (n + gs.length) ∪ {a, b}) ⊆ U := by
          intro i hi
          unfold un at hi
          rw [Finset.mem_biUnion] at hi
          obtain ⟨w, hw, hiw⟩ := hi
          rw [Finset.mem_union, Finset.mem_erase] at hw
          rcases hw with ⟨hwm, hw⟩ | hw
          · apply hsub
            unfold un
            rw [Finset.mem_biUnion]
            exact ⟨w, hw, by rw [hold w hwm]; exact hiw⟩
          · apply hTU
            rw [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact Finset.mem_union_left _ hiw
            · exact Finset.mem_union_right _ hiw
        have hih := ih hok0 _ hs2
        have hcard : (ws.erase (n + gs.length) ∪ {a, b}).card ≤ ws.card + 1 := by
          have e1 := Finset.card_union_le (ws.erase (n + gs.length)) {a, b}
          have e2 := Finset.card_erase_of_mem hm
          have e3 : ({a, b} : Finset ℕ).card ≤ 2 :=
            (Finset.card_insert_le _ _).trans (by simp)
          omega
        have hc2 := hcnt2 hTU h2
        have hc3 := Finset.card_le_card hs1
        omega
      · have hs1 : un n (gs ++ [g]) ws ⊆ un n gs (ws.erase (n + gs.length)) ∪
            ((sets n gs).getD a ∅ ∪ (sets n gs).getD b ∅) := by
          intro i hi
          unfold un at hi
          rw [Finset.mem_biUnion] at hi
          obtain ⟨w, hw, hiw⟩ := hi
          rw [Finset.mem_union]
          by_cases hwm : w = n + gs.length
          · right
            rw [hwm, hTg] at hiw
            exact hiw
          · left
            unfold un
            rw [Finset.mem_biUnion]
            exact ⟨w, Finset.mem_erase.2 ⟨hwm, hw⟩, by rw [← hold w hwm]; exact hiw⟩
        have hs2 : un n gs (ws.erase (n + gs.length)) ⊆ U := by
          intro i hi
          unfold un at hi
          rw [Finset.mem_biUnion] at hi
          obtain ⟨w, hw, hiw⟩ := hi
          rw [Finset.mem_erase] at hw
          apply hsub
          unfold un
          rw [Finset.mem_biUnion]
          exact ⟨w, hw.2, by rw [hold w hw.1]; exact hiw⟩
        have hih := ih hok0 _ hs2
        have e2 := Finset.card_erase_of_mem hm
        have hc3 := (Finset.card_le_card hs1).trans (Finset.card_union_le _ _)
        omega
    · have hs : un n (gs ++ [g]) ws = un n gs ws := by
        unfold un
        apply Finset.biUnion_congr rfl
        intro w hw
        exact hold w (fun h => hm (h ▸ hw))
      rw [hs] at hsub ⊢
      have := ih hok0 ws hsub
      omega

noncomputable def ctr {n : ℕ} [NeZero n] (p : Block n) : Fin n :=
  if p.1.card = 1 then p.1.toList.headD 0 else p.2.toList.headD 0

def lv {n : ℕ} (p : Block n) : Finset (Fin n) := if p.1.card = 1 then p.2 else p.1

lemma single_head {n : ℕ} [NeZero n] (s : Finset (Fin n)) (h : s.card = 1) :
    s = {s.toList.headD 0} := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
  simp

lemma star {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hC4 : PEqualNP.TopForm.NoFourCycle G) (p : Block n) (hb : IsBlock G p) :
    (p.1 = {ctr p} ∧ p.2 = lv p) ∨ (p.2 = {ctr p} ∧ p.1 = lv p) := by
  by_cases h1 : p.1.card = 1
  · left
    have e1 : ctr p = p.1.toList.headD 0 := by simp [ctr, h1]
    have e2 : lv p = p.2 := by simp [lv, h1]
    rw [e1, e2]
    exact ⟨single_head _ h1, rfl⟩
  · right
    have h2 : p.2.card = 1 := by
      by_contra h2
      obtain ⟨_, hne1, hne2, hadj⟩ := hb
      have c1 : 1 < p.1.card := by
        have := Finset.card_pos.2 hne1
        omega
      have c2 : 1 < p.2.card := by
        have := Finset.card_pos.2 hne2
        omega
      obtain ⟨a1, ha1, a2, ha2, hne⟩ := Finset.one_lt_card.1 c1
      obtain ⟨b1, hb1, b2, hb2, hbne⟩ := Finset.one_lt_card.1 c2
      have hsub : ({b1, b2} : Finset (Fin n)) ⊆
          Finset.univ.filter (fun w => G.Adj a1 w ∧ G.Adj a2 w) := by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases hw with rfl | rfl
        · exact ⟨hadj _ ha1 _ hb1, hadj _ ha2 _ hb1⟩
        · exact ⟨hadj _ ha1 _ hb2, hadj _ ha2 _ hb2⟩
      have := (Finset.card_le_card hsub).trans (hC4 a1 a2 hne)
      rw [Finset.card_pair hbne] at this
      omega
    have e1 : ctr p = p.2.toList.headD 0 := by simp [ctr, h1]
    have e2 : lv p = p.1 := by simp [lv, h1]
    rw [e1, e2]
    exact ⟨single_head _ h2, rfl⟩

lemma props {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hC4 : PEqualNP.TopForm.NoFourCycle G) (F : Finset (Block n)) (p : Block n) (hp : p ∈ F)
    (hb : IsBlock G p) :
    (lv p).Nonempty ∧ (∀ v ∈ lv p, G.Adj (ctr p) v) ∧ lv p ∈ sides F ∧
      ∀ u v, BlockCovers p u v → (u = ctr p ∧ v ∈ lv p) ∨ (v = ctr p ∧ u ∈ lv p) := by
  have hs := star G hC4 p hb
  obtain ⟨_, hne1, hne2, hadj⟩ := hb
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨by rw [← h2]; exact hne2, fun v hv => hadj _ (by rw [h1]; exact Finset.mem_singleton_self _) _
      (by rw [h2]; exact hv), ?_, ?_⟩
    · unfold sides
      rw [Finset.mem_union]
      right
      rw [← h2]
      exact Finset.mem_image_of_mem _ hp
    · intro u v hc
      unfold BlockCovers at hc
      rw [h1, h2] at hc
      simp only [Finset.mem_singleton] at hc
      exact hc
  · refine ⟨by rw [← h2]; exact hne1, fun v hv => (hadj v (by rw [h2]; exact hv) (ctr p)
      (by rw [h1]; exact Finset.mem_singleton_self _)).symm, ?_, ?_⟩
    · unfold sides
      rw [Finset.mem_union]
      left
      rw [← h2]
      exact Finset.mem_image_of_mem _ hp
    · intro u v hc
      unfold BlockCovers at hc
      rw [h1, h2] at hc
      simp only [Finset.mem_singleton] at hc
      rcases hc with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact Or.inr ⟨a2, a1⟩
      · exact Or.inl ⟨a2, a1⟩

noncomputable def Fu {n : ℕ} [NeZero n] (F : Finset (Block n)) (u : Fin n) : Finset (Block n) :=
  F.filter (fun p => ctr p = u)

noncomputable def Uu {n : ℕ} [NeZero n] (F : Finset (Block n)) (u : Fin n) : Finset (Fin n) :=
  (Fu F u).biUnion lv

theorem main {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : ℕ)
    (hC4 : PEqualNP.TopForm.NoFourCycle G) (hS : HasSharedBlockCost G c) : HasBlockCost G c := by
  obtain ⟨F, ⟨hblk, hcov⟩, k, ⟨C, ⟨hOr, hw⟩, hkC⟩, hc⟩ := hS
  have hok : OK n C.gates := hOr
  have hall : allOr C.gates := ok_allOr hok
  choose! wire _ hwc using hw
  have hwire : ∀ p ∈ F, (sets n C.gates).getD (wire (lv p)) ∅ = lv p := fun p hp =>
    computes_set C hall _ _ (hwc _ (props G hC4 F p hp (hblk p hp)).2.2.1)
  have hUadj : ∀ u, ∀ b ∈ Uu F u, G.Adj u b := by
    intro u b hb
    unfold Uu at hb
    rw [Finset.mem_biUnion] at hb
    obtain ⟨p, hp, hbp⟩ := hb
    unfold Fu at hp
    rw [Finset.mem_filter] at hp
    rw [← hp.2]
    exact (props G hC4 F p hp.1 (hblk p hp.1)).2.1 b hbp
  let Z := F.image ctr
  let F' := Z.image (fun u => (({u} : Finset (Fin n)), Uu F u))
  have inj : Function.Injective (fun u : Fin n => (({u} : Finset (Fin n)), Uu F u)) := by
    intro u v h
    have := congrArg Prod.fst h
    simpa using this
  refine ⟨F', ⟨?_, ?_⟩, ?_⟩
  · intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨u, hu, rfl⟩ := hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨?_, Finset.singleton_nonempty _, ?_, ?_⟩
    · show Disjoint ({ctr p} : Finset (Fin n)) (Uu F (ctr p))
      rw [Finset.disjoint_singleton_left]
      intro hmem
      exact G.irrefl (hUadj _ _ hmem)
    · show (Uu F (ctr p)).Nonempty
      obtain ⟨x, hx⟩ := (props G hC4 F p hp (hblk p hp)).1
      exact ⟨x, Finset.mem_biUnion.2 ⟨p, Finset.mem_filter.2 ⟨hp, rfl⟩, hx⟩⟩
    · show ∀ a ∈ ({ctr p} : Finset (Fin n)), ∀ b ∈ Uu F (ctr p), G.Adj a b
      intro a ha b hb
      rw [Finset.mem_singleton] at ha
      subst ha
      exact hUadj _ _ hb
  · intro u v huv
    obtain ⟨p, hp, hcp⟩ := hcov u v huv
    refine ⟨(({ctr p} : Finset (Fin n)), Uu F (ctr p)),
      Finset.mem_image.2 ⟨ctr p, Finset.mem_image_of_mem _ hp, rfl⟩, ?_⟩
    have hmemU : ∀ x ∈ lv p, x ∈ Uu F (ctr p) := fun x hx =>
      Finset.mem_biUnion.2 ⟨p, Finset.mem_filter.2 ⟨hp, rfl⟩, hx⟩
    unfold BlockCovers
    rcases (props G hC4 F p hp (hblk p hp)).2.2.2 u v hcp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Finset.mem_singleton.2 h1, hmemU v h2⟩
    · exact Or.inr ⟨Finset.mem_singleton.2 h1, hmemU u h2⟩
  · have hsum : ∑ q ∈ F', blockCost q = ∑ u ∈ Z, (Uu F u).card := by
      rw [Finset.sum_image (by intro x _ y _ h; exact inj h)]
      apply Finset.sum_congr rfl
      intro u _
      simp [blockCost]
    have hcard : F'.card = Z.card := Finset.card_image_of_injective _ inj
    have hZ : Z.card ≤ F.card := Finset.card_image_le
    have hF : F.card = ∑ u ∈ Z, (Fu F u).card :=
      Finset.card_eq_sum_card_fiberwise (by intro p hp; exact Finset.mem_image_of_mem ctr hp)
    have hU : ∀ u ∈ Z, (Uu F u).card ≤ (Gu n C.gates (Uu F u)).card + (Fu F u).card := by
      intro u _
      have e : un n C.gates ((Fu F u).image (fun p => wire (lv p))) = Uu F u := by
        unfold un Uu
        rw [Finset.image_biUnion]
        apply Finset.biUnion_congr rfl
        intro p hp
        exact hwire p (Finset.mem_filter.1 hp).1
      have h := count_main n (Uu F u) C.gates hok _ (by intro i hi; rw [e] at hi; exact hi)
      rw [e] at h
      have := Finset.card_image_le (s := Fu F u) (f := fun p => wire (lv p))
      omega
    have disj : ∀ u v : Fin n, u ≠ v →
        Disjoint (Gu n C.gates (Uu F u)) (Gu n C.gates (Uu F v)) := by
      intro u v huv
      rw [Finset.disjoint_left]
      intro j hju hjv
      unfold Gu at hju hjv
      rw [Finset.mem_filter] at hju hjv
      have hsub : (sets n C.gates).getD (n + j) ∅ ⊆
          Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
        intro i hi
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hUadj u i (hju.2.1 hi), hUadj v i (hjv.2.1 hi)⟩
      have h3 := (Finset.card_le_card hsub).trans (hC4 u v huv)
      have h4 := hju.2.2
      omega
    have hbu : (Z.biUnion (fun u => Gu n C.gates (Uu F u))).card =
        ∑ u ∈ Z, (Gu n C.gates (Uu F u)).card :=
      Finset.card_biUnion (by intro u _ v _ huv; exact disj u v huv)
    have hG : ∑ u ∈ Z, (Gu n C.gates (Uu F u)).card ≤ C.gates.length := by
      rw [← hbu]
      calc (Z.biUnion (fun u => Gu n C.gates (Uu F u))).card
          ≤ (Finset.range C.gates.length).card :=
            Finset.card_le_card (Finset.biUnion_subset.2 (fun u _ => Finset.filter_subset _ _))
        _ = C.gates.length := Finset.card_range _
    have hsl : ∑ u ∈ Z, (Uu F u).card ≤
        ∑ u ∈ Z, ((Gu n C.gates (Uu F u)).card + (Fu F u).card) := Finset.sum_le_sum hU
    rw [Finset.sum_add_distrib] at hsl
    unfold familyCost
    rw [hsum, hcard]
    omega

end PEqualNP.Outside.L_meta_4915

theorem PEqualNP.Outside.L_meta_4915 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : ℕ), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x4 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x4 := by
  intro n G _ c hC4 hS
  by_cases hn : n = 0
  · refine ⟨∅, ⟨by simp, fun u _ _ => absurd u.isLt (by omega)⟩, by simp [PEqualNP.BicliqueBlockCost.familyCost]⟩
  · have : NeZero n := ⟨hn⟩
    exact PEqualNP.Outside.L_meta_4915.main G c hC4 hS
