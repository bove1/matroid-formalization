import MatroidFormalization.Defs

/-
  This file is where I'm burying all of the lemmas for the things I
  actually did get around to proving. I didn't really do a good job naming
  these, but it follows a pretty simple structure. x_lemi is the ith
  lemma I needed about the X definition for matroids. x_yi is the
  proof of the ith axiom for the y definition in the conversion from the
  x definition.

  I recommend closing all of the lemmas and examining them one at a time.
-/

-- This essentially proves the downward closedness of independent sets,
-- in the case where the difference I1 ⊆ I2 is only one element.
lemma rank_lem {α : Type} [DecidableEq α] (rmat : RMatroid α) :
  ∀I1 ∈ rmat.E.powerset, ∀I2 ∈ rmat.E.powerset,
  rmat.rk I1 = #I1 → I2 ⊆ I1 →
  #I1 = #I2 + 1 →
  rmat.rk I2 = #I2 := by
    intro I1 hI1 I2 hI2 hind hsub hcard
    have h : rmat.rk I2 ≤ #I2 ∧ rmat.rk I2 ≥ #I2 →
      rmat.rk I2 = #I2 := by
      intro h1
      let h2 := h1.left
      have h3 := h1.right
      linarith
    apply h
    apply And.intro
    exact RMatroid.r1 I2 hI2
    have h : #(I1 \ I2) = 1 := calc
      #(I1 \ I2) = #I1 - #I2 :=
        Finset.card_sdiff hsub
      _= (#I2 + 1) - #I2 := by rw [hcard]
      _= 1 := by
        simp only [ge_iff_le, add_le_iff_nonpos_right, add_tsub_cancel_left]
    have h := Finset.card_eq_one.mp h
    apply Exists.elim h
    intro e he
    have h: I1 = I2 ∪ {e} := by
      rw [he.symm]
      exact (Finset.union_sdiff_of_subset hsub).symm
    have h2 : e ∈ I1 \ I2 := by simp only [he, Finset.mem_singleton]
    have h2: e ∈ I1 := (Finset.mem_sdiff.mp h2).left
    simp only [Finset.mem_powerset] at hI1
    have h2: e ∈ RMatroid.E := by
      rename_i inst h_1 h_2 h_3
      aesop_subst h
      simp_all only [Finset.mem_powerset, ge_iff_le, and_imp, Finset.disjoint_singleton_right, Finset.card_singleton,
        Finset.singleton_inj, exists_eq', Finset.mem_singleton, Finset.mem_union, or_true]
      apply hI1
      simp_all only [Finset.disjoint_singleton_right, Finset.mem_union, Finset.mem_singleton, or_true]
    have h3 := (RMatroid.r3 I2 hI2 e h2).right
    rw [h.symm, hind, hcard] at h3
    linarith

-- This uses the previous result to extend downward closedness to
-- arbitrary subsets.
lemma rank_lem2 {α : Type} [DecidableEq α] (rmat : RMatroid α) (n : ℕ) :
  ∀I1 ∈ rmat.E.powerset, ∀I2 ∈ rmat.E.powerset,
  rmat.rk I1 = #I1 → I2 ⊆ I1 →
  #I1 - #I2 = n →
  rmat.rk I2 = #I2 :=
  by
    intro I1 hI1 I2 hI2 hcard hsub hn
    have hI2c := hI2
    simp only [Finset.mem_powerset] at hI2
    simp only [Finset.mem_powerset] at hI1
    induction n generalizing I2 with
    | zero =>
      have h1 : #I1 ≤ #I2 := by
        simp only [ge_iff_le, Nat.zero_eq, tsub_eq_zero_iff_le] at hn
        linarith
      have h2 : I2 = I1 := Finset.eq_of_subset_of_card_le hsub h1
      rw [h2.symm] at hcard
      exact hcard
    | succ m h =>
      have h1 : #I1 - #I2 > 0 :=
        by simp only [ge_iff_le, hn, gt_iff_lt, Nat.succ_pos']
      have h2 : #(I1 \ I2) + #I2 = #I1 :=
        Finset.card_sdiff_add_card_eq_card hsub
      have h2 : #(I1 \ I2) = #I1 - #I2 := calc
        #(I1 \ I2) = #(I1 \ I2) + 0 := by simp only [add_zero]
        _= #(I1 \ I2) + #I2 - #I2 :=
          by simp only [add_zero, ge_iff_le,
            add_le_iff_nonpos_left, nonpos_iff_eq_zero, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset,
            add_tsub_cancel_right]
        _= #I1 - #I2 := by simp only [h2, ge_iff_le]
      rw [h2.symm] at h1
      have h3 : Finset.Nonempty (I1 \ I2) := Finset.card_pos.mp h1
      have h3 := Finset.Nonempty.bex h3
      apply Exists.elim h3
      intro e he
      let I3 := I2 ∪ {e}
      have h3 : e ∉ I2 := (Finset.mem_sdiff.mp he).right
      have h3 : Disjoint I2 {e} :=
        Finset.disjoint_singleton_right.mpr h3
      have h2 : #I3 = #I2 + 1 := calc
        #I3 = #(I2 ∪ {e}) := by rw []
        _= #(I2) + #({e}) := Finset.card_disjoint_union h3
        _= #I2 + 1 := by simp only [Finset.card_singleton]
      have h3 : #I1 - #I3 = m := calc
        #I1 - #I3
        = #I1 - (#I2 + 1) := by
          rw [h2]
        _= #I1 - #I2 - 1 := by
          simp only [ge_iff_le, Nat.sub_add_eq, tsub_le_iff_right]
        _= m.succ - 1 := by
          rw [hn]
      have h6 : e ∈ I1 := (Finset.mem_sdiff.mp he).left
      have h4 : I3 ⊆ RMatroid.E := by
        apply Finset.union_subset hI2
        apply Finset.singleton_subset_iff.mpr
        have h5 : e ∈ I1 := (Finset.mem_sdiff.mp he).left
        apply hI1
        exact h5
      have h7 : I3 ∈ RMatroid.E.powerset := by
        simp only [Finset.mem_powerset, h4]
      have h5 : I3 ⊆ I1 := by
        apply Finset.union_subset hsub
        apply Finset.singleton_subset_iff.mpr
        exact h6
      have h1 : RMatroid.rk I3 = #I3 :=
        h I3 h5 h3 h7 h4
      have h8 : I2 ⊆ I3 := by
        simp only
        exact Finset.subset_union_left I2 {e}
      exact rank_lem rmat I3 h7 I2 hI2c h1 h8 h2

-- This applies the previous result.
lemma rank_lem3 {α : Type} [DecidableEq α] (rmat : RMatroid α) :
  ∀I1 ∈ rmat.E.powerset, ∀I2 ∈ rmat.E.powerset,
  rmat.rk I1 = #I1 → I2 ⊆ I1 →
  rmat.rk I2 = #I2 := by
  intro I1 hI1 I2 hI2 hcard hsub
  let n := #I1 - #I2
  have h: #I1 - #I2 = n := by simp only [ge_iff_le]
  exact rank_lem2 rmat n I1 hI1 I2 hI2 hcard hsub h

-- I honestly don't remember what this proof (or the rest of
-- the rank lemmas) means.
lemma rank_lem4 {α : Type} [DecidableEq α] (rmat : RMatroid α) :
  ∀B ∈ RMatroid.E.powerset, ∀A ∈ rmat.E.powerset,
  B ⊆ A → (∀e ∈ A, RMatroid.rk (B) = RMatroid.rk (B ∪ {e})) → ∀f ∈ A,
  ∀e ∈ A, RMatroid.rk (B ∪ {f}) = RMatroid.rk ((B ∪ {f}) ∪ {e}) :=
  by
    intro B hB A hA hsub hrk f hf e he
    simp only [Finset.mem_powerset] at hB
    simp only [Finset.mem_powerset] at hA
    apply Or.elim (Classical.em (f ∈ B))
    intro hfB
    have h1 : B ∪ {f} = B := by simp only [Finset.union_eq_left_iff_subset,
      Finset.singleton_subset_iff, hfB]
    rw [h1]
    exact (hrk e he)
    intro hfnB
    apply Or.elim (Classical.em (e ∈ B))
    intro heB
    have h1 : B ∪ {e} = B := by simp only [Finset.union_eq_left_iff_subset,
      Finset.singleton_subset_iff, heB]
    have h2 : B ∪ {f} ∪ {e} = B ∪ {f} := calc
      B ∪ {f} ∪ {e} = B ∪ ({f} ∪ {e}) := by simp only [Finset.union_assoc]
      _= B ∪ ({e} ∪ {f}) := by simp only [Finset.union_comm]
      _= B ∪ {e} ∪ {f} := by simp only [Finset.union_assoc]
      _= B ∪ {f} := by simp only [h1]
    rw [h2]
    intro henB
    apply Or.elim (Classical.em (e = f))
    intro hef
    rw [hef]
    have h3 : {f} ∪ {f} = {f} := Finset.union_self {f}
    calc
      RMatroid.rk (B ∪ {f}) = RMatroid.rk (B ∪ ({f} ∪ {f})) := by
        simp only [Finset.union_idempotent]
      _= RMatroid.rk (B ∪ {f} ∪ {f}) := by simp only [Finset.union_assoc]
    intro hnef
    have h1 : B ∪ {f} ∈ RMatroid.E.powerset := by
      simp only [Finset.mem_powerset]
      apply Finset.union_subset hB
      simp only [Finset.singleton_subset_iff]
      apply hA
      exact hf
    have h1' : B ∪ {e} ∈ RMatroid.E.powerset := by
      simp only [Finset.mem_powerset]
      apply Finset.union_subset hB
      simp only [Finset.singleton_subset_iff]
      apply hA
      exact he
    have h5 : e ∈ RMatroid.E := by
      apply hA
      exact he
    let h4 := RMatroid.r3 (B ∪ {f}) h1 e h5
    apply Or.elim (Classical.em
      (RMatroid.rk (B ∪ {f}) = RMatroid.rk (B ∪ {f} ∪ {e})))
    simp only [Finset.union_assoc, imp_self]
    intro h5
    let h4l := h4.left
    let h4r := h4.right
    have h6 : RMatroid.rk (B ∪ {f}) < RMatroid.rk (B ∪ {f} ∪ {e}) :=
      Nat.lt_of_le_of_ne h4l h5
    have h7 : RMatroid.rk (B ∪ {f}) + 1 ≤ RMatroid.rk (B ∪ {f} ∪ {e}) := by
      rename_i inst h5_1
      simp_all only [Finset.union_assoc]
      exact h6
    have h7 : RMatroid.rk (B ∪ {f} ∪ {e}) = RMatroid.rk (B ∪ {f}) + 1 := by
      linarith
    rw [(hrk f hf).symm] at h7
    let hB := RMatroid.r2 (B ∪ {f}) h1 (B ∪ {e}) h1'
    rw [(hrk f hf).symm] at hB
    rw [(hrk e he).symm] at hB
    have hBigUnion : B ∪ {f} ∪ (B ∪ {e}) = B ∪ {f} ∪ {e} := calc
      B ∪ {f} ∪ (B ∪ {e}) = B ∪ ({f} ∪ B) ∪ {e} := by simp only [Finset.union_assoc]
      _= B ∪ (B ∪ {f}) ∪ {e} := by simp only [Finset.union_comm]
      _= (B ∪ B) ∪ {f} ∪ {e} := by simp only [Finset.union_assoc]
      _= B ∪ {f} ∪ {e} := by simp only [Finset.union_self]
    have hBigInt : (B ∪ {f}) ∩ (B ∪ {e}) = B := calc
      (B ∪ {f}) ∩ (B ∪ {e}) = (B ∩ (B ∪ {e})) ∪ ({f} ∩ (B ∪ {e})) := by
        simp only [Finset.inter_distrib_right]
      _= (B ∩ ({e} ∪ B)) ∪ ({f} ∩ (B ∪ {e})) := by simp only [Finset.union_comm]
      _= B ∪ ({f} ∩ (B ∪ {e})) := by simp only [Finset.inter_union_self]
      _= B ∪ (({f} ∩ B) ∪ ({f} ∩ {e})) := by simp only [Finset.inter_distrib_left]
      _= B ∪ (∅ ∪ ({f} ∩ {e})) := by simp only [hfnB, not_false_eq_true,
        Finset.singleton_inter_of_not_mem,
        Finset.mem_singleton, Finset.empty_union]
      _= B ∪ (∅ ∪ ∅) := by simp only [Finset.mem_singleton, hnef, not_false_eq_true,
        Finset.inter_singleton_of_not_mem, Finset.union_idempotent, Finset.union_empty]
      _= B ∪ ∅ := by simp only [Finset.union_idempotent, Finset.union_empty]
      _= B := by simp only [Finset.union_empty]
    rw [hBigUnion, hBigInt, h7] at hB
    apply False.elim
    linarith

lemma rank_lem5 {α : Type} [DecidableEq α] (rmat : RMatroid α) (n : ℕ):
  ∀B ∈ RMatroid.E.powerset, ∀A ∈ rmat.E.powerset, ∀C ∈ rmat.E.powerset,
  B ⊆ A → (∀e ∈ A, RMatroid.rk (B) = RMatroid.rk (B ∪ {e})) → B ⊆ C →
  C ⊆ A → #C - #B = n →
  ∀e ∈ A, RMatroid.rk (C) = RMatroid.rk (C ∪ {e}) :=
  by
    intro B hB A hA C hC hsub1 hrk hsub2 hsub3 hcard
    induction n generalizing C with
    | zero =>
      have hBgeC : #C ≤ #B :=
        by
          rename_i inst
          simp_all only [Finset.mem_powerset, ge_iff_le,
          Nat.zero_eq, tsub_eq_zero_iff_le]
      have hEq : B = C := Finset.eq_of_subset_of_card_le hsub2 hBgeC
      rw [hEq.symm]
      exact hrk
    | succ m hm =>
      have h1 : #C - #B > 0 :=
        by simp only [ge_iff_le, hcard, gt_iff_lt, Nat.succ_pos']
      have h2 : #(C \ B) + #B = #C :=
        Finset.card_sdiff_add_card_eq_card hsub2
      have h2 : #(C \ B) = #C - #B := calc
        #(C \ B) = #(C \ B) + 0 := by simp only [add_zero]
        _= #(C \ B) + #B - #B :=
          by simp only [add_zero, ge_iff_le,
            add_le_iff_nonpos_left, nonpos_iff_eq_zero, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset,
            add_tsub_cancel_right]
        _= #C - #B := by simp only [h2, ge_iff_le]
      rw [h2.symm] at h1
      have h3 : Finset.Nonempty (C \ B) := Finset.card_pos.mp h1
      have h3 := Finset.Nonempty.bex h3
      apply Exists.elim h3
      intro e he
      have hCmInA : C \ {e} ⊆ A  := by
        simp only [Finset.mem_powerset]
        intro t ht
        have h : t ∈ C := by
          rename_i inst h2_1 h3_1
          simp_all only [Finset.mem_powerset, Finset.Subset.refl, Nat.sub_self, ge_iff_le, gt_iff_lt, Nat.succ_pos',
          Finset.mem_sdiff, not_true, Finset.mem_singleton]
        apply hsub3
        exact h
      have hCmInPow : C \ {e} ∈ RMatroid.E.powerset := by
        simp only [Finset.mem_powerset]
        simp only [Finset.mem_powerset] at hA
        intro t ht
        apply hA
        apply hCmInA
        exact ht
      have bSubCm : B ⊆ C \ {e} := by
        intro b hb
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        apply And.intro
        apply hsub2
        exact hb
        intro hEq
        rename_i inst h2_1 h3_1
        aesop_subst hEq
        simp_all only [Finset.mem_powerset, Finset.Subset.refl,
          Nat.sub_self, ge_iff_le, gt_iff_lt, Nat.succ_pos',
          Finset.mem_sdiff, not_true, and_false]
      have eInC : e ∈ C := by
        rename_i inst h2_1 h3_1
        simp_all only [Finset.mem_powerset, Finset.Subset.refl,
          Nat.sub_self, ge_iff_le, gt_iff_lt, Nat.succ_pos',
          Finset.mem_sdiff, not_true]
      have singletonSub : {e} ⊆ C := by
        simp only [Finset.singleton_subset_iff]
        exact eInC
      have card_diff :
        #(C \ {e}) = #C - #{e} :=
        Finset.card_sdiff singletonSub
      have card_diff2 : #(C \ {e}) - #B = m := calc
        #(C \ {e}) - #B
        = #C - #{e} - #B := by
          simp only [card_diff]
        _= #C - 1 - #B :=
          by simp only [Finset.card_singleton, ge_iff_le,
          tsub_le_iff_right]
        _= #C - #B - 1 := by
          simp only [Nat.sub_right_comm]
        _= Nat.succ m - 1 := by simp only [hcard]
        _= m := by simp only [ge_iff_le, Nat.le_succ,
          nonpos_iff_eq_zero, Nat.succ_sub_succ_eq_sub, tsub_zero]
      have heInA : e ∈ A := by
        apply hsub3
        exact eInC
      have hCmunionu : C \ {e} ∪ {e} = C := by
        simp only [Finset.sdiff_union_self_eq_union,
          Finset.union_eq_left_iff_subset, Finset.singleton_subset_iff]
        exact eInC
      have littleInduction :=
        hm (C \ {e}) hCmInPow bSubCm hCmInA card_diff2
      have bigInduction :=
        rank_lem4 rmat (C \ {e}) hCmInPow A hA hCmInA littleInduction
        e heInA
      rw [hCmunionu] at bigInduction
      exact bigInduction

lemma rank_lem6 {α : Type} [DecidableEq α] (rmat : RMatroid α) (n : ℕ):
  ∀B ∈ RMatroid.E.powerset, ∀A ∈ rmat.E.powerset, ∀C ∈ rmat.E.powerset,
  B ⊆ A → (∀e ∈ A, RMatroid.rk (B) = RMatroid.rk (B ∪ {e})) → B ⊆ C →
  C ⊆ A → #C - #B = n →
  RMatroid.rk C = RMatroid.rk B :=
  by
    intro B hB A hA C hC hsub1 hrk hsub2 hsub3 hcard
    induction n generalizing C with
    | zero =>
      have hBgeC : #C ≤ #B :=
        by
          rename_i inst
          simp_all only [Finset.mem_powerset, ge_iff_le,
          Nat.zero_eq, tsub_eq_zero_iff_le]
      have hEq : B = C := Finset.eq_of_subset_of_card_le hsub2 hBgeC
      rw [hEq]
    | succ m hm =>
      have h1 : #C - #B > 0 :=
        by simp only [ge_iff_le, hcard, gt_iff_lt, Nat.succ_pos']
      have h2 : #(C \ B) + #B = #C :=
        Finset.card_sdiff_add_card_eq_card hsub2
      have h2 : #(C \ B) = #C - #B := calc
        #(C \ B) = #(C \ B) + 0 := by simp only [add_zero]
        _= #(C \ B) + #B - #B :=
          by simp only [add_zero, ge_iff_le,
            add_le_iff_nonpos_left, nonpos_iff_eq_zero, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset,
            add_tsub_cancel_right]
        _= #C - #B := by simp only [h2, ge_iff_le]
      rw [h2.symm] at h1
      have h3 : Finset.Nonempty (C \ B) := Finset.card_pos.mp h1
      have h3 := Finset.Nonempty.bex h3
      apply Exists.elim h3
      intro e he
      have hCmInA : C \ {e} ⊆ A  := by
        simp only [Finset.mem_powerset]
        intro t ht
        have h : t ∈ C := by
          rename_i inst h2_1 h3_1
          simp_all only [Finset.mem_powerset, Finset.Subset.refl, Nat.sub_self, ge_iff_le, gt_iff_lt, Nat.succ_pos',
          Finset.mem_sdiff, not_true, Finset.mem_singleton]
        apply hsub3
        exact h
      have hCmInPow : C \ {e} ∈ RMatroid.E.powerset := by
        simp only [Finset.mem_powerset]
        simp only [Finset.mem_powerset] at hA
        intro t ht
        apply hA
        apply hCmInA
        exact ht
      have bSubCm : B ⊆ C \ {e} := by
        intro b hb
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        apply And.intro
        apply hsub2
        exact hb
        intro hEq
        rename_i inst h2_1 h3_1
        aesop_subst hEq
        simp_all only [Finset.mem_powerset, Finset.Subset.refl,
          Nat.sub_self, ge_iff_le, gt_iff_lt, Nat.succ_pos',
          Finset.mem_sdiff, not_true, and_false]
      have eInC : e ∈ C := by
        rename_i inst h2_1 h3_1
        simp_all only [Finset.mem_powerset, Finset.Subset.refl,
          Nat.sub_self, ge_iff_le, gt_iff_lt, Nat.succ_pos',
          Finset.mem_sdiff, not_true]
      have singletonSub : {e} ⊆ C := by
        simp only [Finset.singleton_subset_iff]
        exact eInC
      have card_diff :
        #(C \ {e}) = #C - #{e} :=
        Finset.card_sdiff singletonSub
      have card_diff2 : #(C \ {e}) - #B = m := calc
        #(C \ {e}) - #B
        = #C - #{e} - #B := by
          simp only [card_diff]
        _= #C - 1 - #B :=
          by simp only [Finset.card_singleton, ge_iff_le,
          tsub_le_iff_right]
        _= #C - #B - 1 := by
          simp only [Nat.sub_right_comm]
        _= Nat.succ m - 1 := by simp only [hcard]
        _= m := by simp only [ge_iff_le, Nat.le_succ,
          nonpos_iff_eq_zero, Nat.succ_sub_succ_eq_sub, tsub_zero]
      have heInA : e ∈ A := by
        apply hsub3
        exact eInC
      have hCmunionu : C \ {e} ∪ {e} = C := by
        simp only [Finset.sdiff_union_self_eq_union,
          Finset.union_eq_left_iff_subset, Finset.singleton_subset_iff]
        exact eInC
      have littleInduction :=
        hm (C \ {e}) hCmInPow bSubCm hCmInA card_diff2
      have bigInduction :=
        rank_lem5 rmat m B hB A hA (C \ {e}) hCmInPow hsub1 hrk
        bSubCm hCmInA card_diff2 e heInA
      rw [hCmunionu] at bigInduction
      rw [littleInduction.symm]
      rw [bigInduction]

lemma rank_lem7 (α : Type) [DecidableEq α] (rmat : RMatroid α) :
  ∀B ∈ RMatroid.E.powerset, ∀A ∈ rmat.E.powerset,
  B ⊆ A → (∀e ∈ A, RMatroid.rk (B) = RMatroid.rk (B ∪ {e})) →
  RMatroid.rk B = RMatroid.rk A := by
    intro B hB A hA hsub hrk
    let m := #A - #B
    have hmDef : m = #A - #B := by
      simp only [ge_iff_le]
    have bigInduction := rank_lem6 rmat m B hB A hA A hA hsub hrk hsub
      (Finset.Subset.refl A) (hmDef)
    exact bigInduction.symm

lemma rank_lem8 (α : Type) [DecidableEq α] (rmat : RMatroid α) (n : ℕ):
  ∀B ∈ RMatroid.E.powerset, ∀A ∈ rmat.E.powerset,
  B ⊆ A → #A - #B = n → RMatroid.rk B ≤ RMatroid.rk A :=
  by
    intro B hB A hA hsub hcard
    induction n generalizing B with
    | zero =>
      have hAgeB : #A ≤ #B :=
        by
          rename_i inst
          simp_all only [Finset.mem_powerset, ge_iff_le,
          Nat.zero_eq, tsub_eq_zero_iff_le]
      have hEq : B = A := Finset.eq_of_subset_of_card_le hsub hAgeB
      rw [hEq]
    | succ m hm =>
      have h1 : #A - #B > 0 :=
        by simp only [ge_iff_le, hcard, gt_iff_lt, Nat.succ_pos']
      have h2 : #(A \ B) + #B = #A :=
        Finset.card_sdiff_add_card_eq_card hsub
      have h2 : #(A \ B) = #A - #B := calc
        #(A \ B) = #(A \ B) + 0 := by simp only [add_zero]
        _= #(A \ B) + #B - #B :=
          by simp only [add_zero, ge_iff_le,
            add_le_iff_nonpos_left, nonpos_iff_eq_zero, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset,
            add_tsub_cancel_right]
        _= #A - #B := by simp only [h2, ge_iff_le]
      rw [h2.symm] at h1
      have h3 : Finset.Nonempty (A \ B) := Finset.card_pos.mp h1
      have h3 := Finset.Nonempty.bex h3
      apply Exists.elim h3
      intro e he
      have heInA := (Finset.mem_sdiff.mp he).left
      have heInE : e ∈ RMatroid.E := by
        simp only [Finset.mem_powerset] at hA
        apply hA
        exact heInA
      have hsubsE : B ∪ {e} ∈ rmat.E.powerset := by
        simp only [Finset.mem_powerset]
        intro boe
        rename_i inst h2_1 h3_1
        intro a
        simp_all only [Finset.mem_powerset, ge_iff_le, gt_iff_lt,
          Nat.succ_pos', Finset.mem_sdiff, true_and, Finset.mem_union,
          Finset.mem_singleton]
        unhygienic with_reducible aesop_destruct_products
        unhygienic aesop_cases a
        · apply hB
          simp_all only [ge_iff_le]
        · aesop_subst h
          simp_all only [ge_iff_le]
      have hsubsA : B ∪ {e} ⊆ A := by
        intro boe
        simp only [Finset.mem_union, Finset.mem_singleton]
        intro hand
        apply Or.elim hand
        intro hboeB
        apply hsub
        exact hboeB
        intro hboee
        rw [hboee]
        exact heInA
      have hdisj : Disjoint B {e} := by
        simp only [Finset.disjoint_singleton_right]
        exact (Finset.mem_sdiff.mp he).right
      have hcardU : #A - #(B ∪ {e}) = m := calc
        #A - #(B ∪ {e})
        = #A - (#B + #{e}) := by
          rename_i inst h2_1 h3_1
          simp_all only [Finset.mem_powerset, ge_iff_le, gt_iff_lt, Nat.succ_pos',
            Finset.mem_sdiff, true_and, Finset.disjoint_singleton_right,
            not_false_eq_true, Finset.card_disjoint_union, Finset.card_singleton]
        _= #A - (#B + 1) := by
          simp only [Finset.card_singleton, ge_iff_le]
        _= #A - #B - 1 := by
          simp [Nat.sub_add_eq]
        _= m.succ - 1 := by
          simp_all only [Finset.mem_powerset, ge_iff_le, gt_iff_lt, Nat.succ_pos',
            Finset.mem_sdiff, true_and, Finset.disjoint_singleton_right,
            not_false_eq_true, Nat.le_succ, nonpos_iff_eq_zero,
            Nat.succ_sub_succ_eq_sub, tsub_zero]
        _= m := by simp only [ge_iff_le, Nat.le_succ, nonpos_iff_eq_zero,
          Nat.succ_sub_succ_eq_sub, tsub_zero]
      have BigInduction := (rmat.r3 B hB e heInE).left
      have LittleInduction := hm (B ∪ {e}) hsubsE hsubsA hcardU
      exact Nat.le_trans BigInduction LittleInduction

-- No basis is a proper subset of another.
lemma basis_lem1 (α : Type) [DecidableEq α] (bmat : BMatroid α):
  ∀B1 ∈ bmat.basis, ∀B2 ∈ bmat.basis, B1 ⊆ B2 → B1 = B2 := by
  intro B1 hB1 B2 hB2 hsub
  apply Or.elim (Classical.em (B1 = B2))
  simp only [imp_self]
  intro neq
  apply False.elim
  have hnsub : ¬B2 ⊆ B1 := by
    intro haltSub
    apply neq
    exact Finset.Subset.antisymm hsub haltSub
  have hNonempty := Finset.sdiff_nonempty.mpr hnsub
  apply Exists.elim hNonempty
  intro e he
  have bigApp := bmat.b2 B2 hB2 B1 hB1 e he
  apply Exists.elim bigApp
  intro f hf
  have hf := hf.left
  have hDiffEmpt : B1 \ B2 = ∅ := by
    simp only [Finset.sdiff_eq_empty_iff_subset, hsub]
  rw [hDiffEmpt] at hf
  rename_i inst hf_1
  simp_all only [Finset.mem_sdiff, Finset.not_mem_empty, not_true, false_and, exists_false]

-- All bases have the same cardinality.
lemma basis_lem2 (α : Type) [DecidableEq α] (bmat : BMatroid α):
  ∀B1 ∈ bmat.basis, ∀B2 ∈ bmat.basis, #B1 = #B2 := by
  have hInd : ∀n : ℕ, ∀B1 ∈ bmat.basis, ∀B2 ∈ bmat.basis,
    #B1 - #(B1 ∩ B2) = n → #B1 = #B2 := by
    intro n
    induction n with
    | zero =>
      intro B1 hB1 B2 hB2 hcard
      have hcard : #B1 ≤ #(B1 ∩ B2) := by
        rename_i inst
        simp_all only [ge_iff_le, Nat.zero_eq, tsub_eq_zero_iff_le]
      have hsubsinter : B1 ∩ B2 ⊆ B1 := by simp only [Finset.inter_subset_left]
      have hinterEq : B1 ∩ B2 = B1 := Finset.eq_of_subset_of_card_le hsubsinter hcard
      have hsubs : B1 ⊆ B2 := by
        intro e he
        rw [hinterEq.symm] at he
        simp only [Finset.mem_inter] at he
        exact he.right
      have lem1Res : B1 = B2 := basis_lem1 α bmat B1 hB1 B2 hB2 hsubs
      rw [lem1Res]
    | succ m hm =>
      intro B1 hB1 B2 hB2 hcard
      apply Or.elim (Classical.em ¬(B1 \ B2).Nonempty)
      intro empty
      have empty : B1 \ B2 = ∅ := by
        rename_i inst
        simp_all only [ge_iff_le, Finset.not_nonempty_iff_eq_empty,
        Finset.sdiff_eq_empty_iff_subset]
      have hsub := Finset.sdiff_eq_empty_iff_subset.mp empty
      have app := basis_lem1 α bmat B1 hB1 B2 hB2 hsub
      rw [app]
      simp only [Finset.not_nonempty_iff_eq_empty]
      intro hnNon
      have hnNon : (B1 \ B2).Nonempty := Finset.nonempty_of_ne_empty hnNon
      apply Exists.elim hnNon
      intro e he
      let appl := bmat.b2 B1 hB1 B2 hB2 e he
      apply Exists.elim appl
      intro f hf
      have hExch := hf.right
      have hf := hf.left
      have hdisj : Disjoint (B1 \ {e}) {f} := by
        simp only [Finset.disjoint_singleton_right, Finset.mem_sdiff,
          Finset.mem_singleton, not_and, not_not]
        simp only [Finset.mem_sdiff] at hf
        intro hfB
        apply False.elim
        exact hf.right hfB
      have hsubs : {e} ⊆ B1 := by
        simp only [Finset.singleton_subset_iff]
        simp only [Finset.mem_sdiff] at he
        exact he.left
      have hcardNotZero : #B1 ≥ 1 := calc
        #B1 ≥ #{e} := Finset.card_le_of_subset hsubs
        _= 1 := by simp only [Finset.card_singleton]
      have hcard2 : #(B1 \ {e} ∪ {f}) = #B1 := calc
        #(B1 \ {e} ∪ {f}) = #(B1 \ {e}) + #{f} := Finset.card_disjoint_union hdisj
        _= #(B1 \ {e}) + 1 := by simp only [Finset.card_singleton]
        _= #B1 - #{e} + 1 := by simp only [Finset.card_sdiff hsubs]
        _= #B1 - 1 + 1 := by simp [Finset.card_singleton]
        _= #B1 := by simp only [ge_iff_le, Finset.card_eq_zero,
          Nat.sub_add_cancel hcardNotZero]
      have bigInduction := hm (B1 \ {e} ∪ {f}) hExch B2 hB2
      rw [hcard2.symm]
      apply bigInduction
      rw [hcard2]
      have hSwapInt : (B1 \ {e} ∪ {f}) ∩ B2 = (B1 ∩ B2) ∪ {f} := calc
        (B1 \ {e} ∪ {f}) ∩ B2 = ((B1 \ {e}) ∩ B2) ∪ ({f} ∩ B2) := by
          simp only [Finset.inter_distrib_right]
        _= ((B1 \ {e}) ∩ B2) ∪ {f} := by
          rename_i inst hnNon_1 hf_1
          simp_all only [ge_iff_le, Finset.sdiff_eq_empty_iff_subset, Finset.mem_sdiff,
          and_true, not_false_eq_true, and_self,
            Finset.disjoint_singleton_right, Finset.mem_singleton,
            false_and, Finset.singleton_subset_iff, not_true,
            Finset.card_disjoint_union, Finset.card_singleton,
            Finset.singleton_inter_of_mem]
        _= (B2 ∩ (B1 \ {e})) ∪ {f} := by simp only [Finset.inter_comm]
        _= (B2 ∩ B1) \ {e} ∪ {f} := by simp only [Finset.inter_sdiff]
        _= (B2 ∩ B1) ∪ {f} := by
          rename_i inst hnNon_1 hf_1
          simp_all only [ge_iff_le, Finset.sdiff_eq_empty_iff_subset, Finset.mem_sdiff, and_true, not_false_eq_true, and_self,
            Finset.disjoint_singleton_right, Finset.mem_singleton, false_and, Finset.singleton_subset_iff, not_true,
            Finset.card_disjoint_union, Finset.card_singleton, Finset.mem_inter]
          unhygienic with_reducible aesop_destruct_products
          simp_all only [Finset.mem_sdiff, true_and, ge_iff_le, not_true, Finset.mem_inter, and_true, not_false_eq_true,
            Finset.sdiff_singleton_eq_self]
        _= (B1 ∩ B2) ∪ {f} := by simp only [Finset.inter_comm]
      rw [hSwapInt]
      have uniondisj : Disjoint (B1 ∩ B2) {f} := by
        simp only [Finset.disjoint_singleton_right, Finset.mem_inter, not_and]
        intro finB
        apply False.elim
        simp only [Finset.mem_sdiff] at hf
        exact hf.right finB
      have disjCard : #(B1 ∩ B2 ∪ {f}) = #(B1 ∩ B2) + 1 := calc
        #(B1 ∩ B2 ∪ {f}) = #(B1 ∩ B2) + #{f} := by
          rename_i inst hnNon_1 hf_1
          simp_all only [ge_iff_le, Finset.sdiff_eq_empty_iff_subset, Finset.mem_sdiff, and_true, not_false_eq_true, and_self,
            Finset.disjoint_singleton_right, Finset.mem_singleton, false_and, Finset.singleton_subset_iff, not_true,
            Finset.card_disjoint_union, Finset.card_singleton, Finset.mem_inter]
        _= #(B1 ∩ B2) + 1 := by simp only [Finset.card_singleton]
      rw [disjCard]
      have final : #B1 - (#(B1 ∩ B2) + 1) = m := calc
        #B1 - (#(B1 ∩ B2) + 1) = #B1 - #(B1 ∩ B2) - 1 := by
          simp only [ge_iff_le, Nat.sub_add_eq, tsub_le_iff_right]
        _= m.succ - 1 := by simp [hcard]
        _= m := by simp only [ge_iff_le, Nat.le_succ, nonpos_iff_eq_zero,
          Nat.succ_sub_succ_eq_sub, tsub_zero]
      exact final
  intro B1 hB1 B2 hB2
  let n := #B1 - #(B1 ∩ B2)
  have ndef: #B1 - #(B1 ∩ B2) = n := by simp only [ge_iff_le]
  exact hInd n B1 hB1 B2 hB2 ndef

-- Showing maximal independents sets are the same size.
lemma ind_lem1 (α : Type) [DecidableEq α] (imat : IMatroid α) :
  ∀B1 ∈ Finset.filter (fun I1 ↦ ∀ I2 ∈ imat.ind, I1 ⊆ I2 → I1 = I2) imat.ind,
  ∀B2 ∈ Finset.filter (fun I1 ↦ ∀ I2 ∈ imat.ind, I1 ⊆ I2 → I1 = I2) imat.ind,
  #B1 = #B2 := by
    intro B1 hB1 B2 hB2
    simp only [Finset.mem_filter] at hB1
    simp only [Finset.mem_filter] at hB2
    apply Or.elim (Classical.em (#B1 = #B2))
    simp only [imp_self]
    intro contra
    apply False.elim
    have heither: (#B1 < #B2) ∨ (#B2 < #B1) := by
      rename_i inst
      simp_all only [Finset.mem_sdiff, not_true, Finset.sdiff_subset, Finset.mem_powerset, lt_or_lt_iff_ne, ne_eq,
        not_false_eq_true]
    apply Or.elim heither
    intro lt
    let app := imat.i3 B1 hB1.left B2 hB2.left lt
    apply Exists.elim app
    intro e he
    have eInd := he.right
    have he := he.left
    have appl :=
      hB1.right (B1 ∪ {e}) eInd (Finset.subset_union_left B1 {e})
    have hcardf : #B1 = #(B1 ∪ {e}) := by
      rw [appl.symm]
    have hant := (Finset.Subset.antisymm_iff.mp appl).right
    have hr := Finset.union_subset_right hant
    simp only [Finset.singleton_subset_iff] at hr
    simp only [Finset.mem_sdiff] at he
    exact he.right hr
    intro lt
    let app := imat.i3 B2 hB2.left B1 hB1.left lt
    apply Exists.elim app
    intro e he
    have eInd := he.right
    have he := he.left
    have appl :=
      hB2.right (B2 ∪ {e}) eInd (Finset.subset_union_left B2 {e})
    have hcardf : #B2 = #(B2 ∪ {e}) := by
      rw [appl.symm]
    have hant := (Finset.Subset.antisymm_iff.mp appl).right
    have hr := Finset.union_subset_right hant
    simp only [Finset.singleton_subset_iff] at hr
    simp only [Finset.mem_sdiff] at he
    exact he.right hr

-- All independent sets are in maximally independent set.
lemma ind_lem2 {α : Type} [DecidableEq α] {imat : IMatroid α} :
  ∀I ∈ imat.ind, ∃B ∈ Finset.filter (fun I1 ↦ ∀ I2 ∈ imat.ind, I1 ⊆ I2 → I1 = I2) imat.ind,
  I ⊆ B := by
  intro I hI
  let indCond : Finset (Finset α) := Finset.filter (fun I' ↦ I ⊆ I') imat.ind
  let maxInd : ℕ := Finset.fold Nat.max 0 Finset.card indCond
  have hLeqSelf : maxInd ≤ Finset.fold Nat.max 0 Finset.card indCond := by
          simp only [le_refl]
  have hx := (Finset.le_fold_max maxInd).mp hLeqSelf
  apply Or.elim hx
  intro leq0
  have hEq0 : maxInd = 0 := by
    rename_i inst
    simp_all only [le_refl, nonpos_iff_eq_zero, Finset.mem_filter]
  apply Exists.intro ∅
  simp only [Finset.mem_filter]
  have hleq0 : Finset.fold max 0 Finset.card indCond ≤ 0 := by
    rename_i inst
    simp_all only [le_refl, Finset.mem_filter, zero_le, and_true, true_or]
  have lqq00 : 0 ≤ 0 := by linarith
  have iInIncond : I ∈ indCond := by
    simp only [Finset.mem_filter, Finset.Subset.refl, and_true]
    exact hI
  have hBig := ((Finset.fold_max_le 0).mp hleq0).right I iInIncond
  apply And.intro
  apply And.intro
  exact IMatroid.i1
  intro I2 hI2 _
  simp only [nonpos_iff_eq_zero, Finset.card_eq_zero] at hBig
  rw [hBig.symm]
  have hI2cond : I2 ∈ indCond := by
    simp only [Finset.mem_filter]
    apply And.intro
    exact hI2
    rw [hBig]
    rename_i inst a
    aesop_subst hBig
    simp_all only [Finset.empty_subset, implies_true, forall_const,
      Finset.filter_true_of_mem, zero_le, le_refl, and_true,
      true_or]
  have hBig2 := ((Finset.fold_max_le 0).mp hleq0).right I2 hI2cond
  simp only [nonpos_iff_eq_zero, Finset.card_eq_zero] at hBig2
  rw [hBig, hBig2]
  rename_i inst
  simp_all only [le_refl, Finset.mem_filter, zero_le, and_true, true_or,
    Finset.Subset.refl, and_self,
    nonpos_iff_eq_zero, Finset.card_eq_zero]
  intro Ileq
  apply Exists.elim Ileq
  intro B hB
  apply Exists.intro B
  simp only [Finset.mem_filter]
  have hBr := hB.right
  have hBl := hB.left
  simp only [Finset.mem_filter] at hBl
  apply And.intro
  apply And.intro
  exact hBl.left
  intro I2 hI2 hsub
  have hBll := hBl.left
  have hBlr := hBl.right
  have hsubs2 : I ⊆ I2 := by
    intro i hi
    apply hsub
    apply hBlr
    exact hi
  have hCond : I2 ∈ indCond := by
    simp only [Finset.mem_filter]
    exact And.intro hI2 hsubs2
  have hord : #I2 ≤ maxInd :=
    ((Finset.fold_max_le maxInd).mp hLeqSelf).right I2 hCond
  have hTrans : #I2 ≤ #B := Nat.le_trans hord hBr
  exact Finset.eq_of_subset_of_card_le hsub hTrans
  exact hBl.right

lemma b_i3 {α : Type} [DecidableEq α] (bmat : BMatroid α) :
  ∀ (I1 : Finset α),
  I1 ∈ Finset.filter (fun I => ∃ B, B ∈ BMatroid.basis ∧ I ⊆ B) (Finset.powerset BMatroid.E) →
  ∀ (I2 : Finset α),
  I2 ∈ Finset.filter (fun I => ∃ B, B ∈ BMatroid.basis ∧ I ⊆ B) (Finset.powerset BMatroid.E) →
  #I1 < #I2 →
  ∃ e,
  e ∈ I2 \ I1 ∧
  I1 ∪ {e} ∈ Finset.filter (fun I => ∃ B, B ∈ BMatroid.basis ∧ I ⊆ B) (Finset.powerset BMatroid.E) :=
  by
    intro I1 hI1 I2 hI2 hcard
    let hI22 := hI2
    simp only [Finset.mem_powerset, Finset.mem_filter] at hI22
    let hI2r := hI22.right
    apply Exists.elim hI2r
    intro B2 hB2
    have bHype :
      ∀ n : ℕ, (∃B1 ∈ bmat.basis, (I1 ⊆ B1) ∧ #(B1 ∩ (I1 ∪ B2)) ≥ n)
      ∨ ∃ e, e ∈ I2 \ I1 ∧ I1 ∪ {e} ∈
        Finset.filter (fun I => ∃ B, B ∈ bmat.basis ∧ I ⊆ B) bmat.E.powerset := by
      intro n
      induction n with
      | zero =>
        simp only [Finset.mem_powerset, Finset.mem_filter] at hI1
        have hI1r := hI1.right
        apply Exists.elim hI1r
        intro B1 hB1
        apply Or.inl
        apply Exists.intro B1
        apply And.intro
        exact hB1.left
        apply And.intro
        exact hB1.right
        rename_i inst
        simp_all only [Finset.mem_powerset, Finset.mem_filter, and_self,
        and_true, Nat.zero_eq, ge_iff_le, zero_le]
      | succ m hm =>
        apply Or.elim hm
        intro hm
        apply Exists.elim (hm)
        intro B1 hB1
        apply Or.elim (Classical.em (#(B1 ∩ (I1 ∪ B2)) = #B1))
        intro hcard2
        have hsubs : B1 ∩ (I1 ∪ B2) ⊆ B1 :=
          Finset.inter_subset_left B1 (I1 ∪ B2)
        have hEq : B1 ∩ (I1 ∪ B2) = B1 := by
          apply Finset.eq_of_subset_of_card_le hsubs
          rename_i inst
          simp_all only [Finset.mem_powerset, Finset.mem_filter, and_self,
          ge_iff_le, le_refl]
        have hsubs2 : B1 ⊆ I1 ∪ B2 := by
          intro b hb
          rw [hEq.symm] at hb
          simp only [Finset.mem_inter, Finset.mem_union] at hb
          simp only [Finset.mem_union]
          exact hb.right
        have hwha : B2 = I2 ∪ (B2 \ I2) := by
          rename_i inst hm_1
          simp_all only [Finset.mem_powerset, Finset.mem_filter, and_self, ge_iff_le, Finset.mem_sdiff, true_or,
            Finset.Subset.refl, Finset.inter_eq_left_iff_subset, Finset.union_sdiff_self_eq_union,
            Finset.right_eq_union_iff_subset]
        have hwlh : I1 ∪ B2 = I1 ∪ (B2 \ I1) := by
          simp only [Finset.union_sdiff_self_eq_union]
        have hwlh2 : I1 ∪ B2 = I1 ∪ ((I2 ∪ (B2 \ I2)) \ I1) := by
          rw [hwha.symm]
          exact hwlh
        rw [Finset.union_sdiff_distrib] at hwlh2
        rw [hwlh2] at hEq
        have hEq := hEq.symm
        rw [Finset.inter_distrib_left,
          Finset.inter_distrib_left,
          (Finset.union_assoc (B1 ∩ I1) (B1 ∩ (I2 \ I1)) (B1 ∩ ((B2 \ I2) \ I1))).symm,
          (Finset.inter_eq_right_iff_subset I1 B1).mpr hB1.right.left] at hEq
        have hdisj : Disjoint I1 (B1 ∩ (I2 \ I1) ∪ B1 ∩ ((B2 \ I2) \ I1)) := by
          apply Finset.disjoint_iff_inter_eq_empty.mpr
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro nonempt
          apply Exists.elim nonempt
          intro e he
          simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at he
          apply Or.elim he.right
          intro he2
          exact he2.right.right he.left
          intro he2
          exact he2.right.right he.left
        have hdisj2 : Disjoint (B1 ∩ (I2 \ I1)) (B1 ∩ ((B2 \ I2) \ I1)) := by
          apply Finset.disjoint_iff_inter_eq_empty.mpr
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro nonempt
          apply Exists.elim nonempt
          intro e he
          simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at he
          exact he.right.right.left.right he.left.right.left
        have hcardB1 :
          #B1 = #I1 + #(B1 ∩ (I2 \ I1)) + #(B1 ∩ ((B2 \ I2) \ I1)) := calc
          #B1 = #(I1 ∪ B1 ∩ (I2 \ I1) ∪ B1 ∩ ((B2 \ I2) \ I1)) := by
            -- aesop?
            sorry
          _= #I1 + #(B1 ∩ (I2 \ I1)) + #(B1 ∩ ((B2 \ I2) \ I1)) := by sorry
        sorry
        sorry
        sorry
    sorry

lemma b_i1 {α : Type} [DecidableEq α] (bmat : BMatroid α) :
  ∅ ∈ Finset.filter (fun I => ∃ B, B ∈ bmat.basis ∧ I ⊆ B) (bmat.E.powerset) := by
    simp only [Finset.mem_filter, Finset.empty_subset, and_true]
    apply And.intro
    rename_i inst
    simp_all only [Finset.mem_powerset, Finset.empty_subset]
    have b1 := bmat.b1
    have b1 := Finset.nonempty_of_ne_empty b1
    exact b1

lemma b_i2 {α : Type} [DecidableEq α] (bmat : BMatroid α) :
  ∀ (I2 : Finset α),
  I2 ∈ Finset.filter (fun I => ∃ B, B ∈ BMatroid.basis ∧ I ⊆ B) (Finset.powerset BMatroid.E) →
    ∀ (I1 : Finset α),
      I1 ∈ Finset.powerset BMatroid.E →
        I1 ⊆ I2 → I1 ∈ Finset.filter (fun I => ∃ B, B ∈ BMatroid.basis ∧ I ⊆ B) (Finset.powerset BMatroid.E) :=
  by
    intro I2 hI2 I1 hI1 hSub
    simp only [Finset.mem_powerset, Finset.mem_filter] at hI2
    let hI2r := hI2.right
    apply Exists.elim hI2r
    intro B hB
    simp only [Finset.mem_powerset, Finset.mem_filter]
    apply And.intro
    rename_i inst
    simp_all only [Finset.mem_powerset]
    apply Exists.intro B
    apply And.intro hB.left
    exact Finset.Subset.trans hSub hB.right

lemma i_b1 {α : Type} [DecidableEq α] (imat : IMatroid α) :
  Finset.filter (fun I1 => ∀ (I2 : Finset α), I2 ∈ IMatroid.ind → I1 ⊆ I2 → I1 = I2) IMatroid.ind ≠ ∅ := by
    let maxInd : ℕ := Finset.fold Nat.max 0 Finset.card imat.ind
    have hLeqSelf : maxInd ≤ Finset.fold Nat.max 0 Finset.card imat.ind := by
        simp only [le_refl]
    have hx := (Finset.le_fold_max maxInd).mp hLeqSelf
    apply Finset.Nonempty.ne_empty
    apply Or.elim hx
    intro leq0
    have eq0 : maxInd = 0 := by linarith
    apply Exists.intro ∅
    simp only [Finset.mem_filter, Finset.empty_subset, not_true]
    apply And.intro
    exact imat.i1
    intro I hI _
    apply Or.elim (Classical.em (∅ = I))
    simp only [imp_self]
    intro nonempty
    have nonempty : ¬ I = ∅ := by
      rename_i inst a
      simp_all only [le_refl, Finset.mem_filter, zero_le, and_true, true_or]
      apply Aesop.BuiltinRules.not_intro
      intro a
      aesop_subst a
      simp_all only [not_true]
    apply False.elim
    have nonempty := Finset.nonempty_iff_ne_empty.mpr nonempty
    have cardPos := Finset.Nonempty.card_pos nonempty
    have leq02 := ((Finset.fold_max_le 0).mp leq0).right I hI
    linarith
    intro hEx
    apply Exists.elim hEx
    intro I1 hI1
    apply Exists.intro I1
    simp only [Finset.mem_filter]
    apply And.intro
    exact hI1.left
    intro I2 hI2 hsub
    have hImax := hI1.right
    have maxCond := ((Finset.fold_max_le maxInd).mp hLeqSelf).right I2 hI2
    have I2lI1 := Nat.le_trans maxCond hImax
    exact Finset.eq_of_subset_of_card_le hsub I2lI1

lemma i_b2 {α : Type} [DecidableEq α] (imat : IMatroid α) :
  ∀ (B1 : Finset α),
  B1 ∈ Finset.filter (fun I1 => ∀ (I2 : Finset α), I2 ∈ IMatroid.ind → I1 ⊆ I2 → I1 = I2) IMatroid.ind →
    ∀ (B2 : Finset α),
      B2 ∈ Finset.filter (fun I1 => ∀ (I2 : Finset α), I2 ∈ IMatroid.ind → I1 ⊆ I2 → I1 = I2) IMatroid.ind →
        ∀ (e : α),
          e ∈ B1 \ B2 →
            ∃ f,
              f ∈ B2 \ B1 ∧
                B1 \ {e} ∪ {f} ∈
                  Finset.filter (fun I1 => ∀ (I2 : Finset α), I2 ∈ IMatroid.ind → I1 ⊆ I2 → I1 = I2) IMatroid.ind := by
    intro B1 hB1 B2 hB2 e he
    have hB1' := hB1
    have hB2' := hB2
    simp only [Finset.mem_filter] at hB1
    simp only [Finset.mem_filter] at hB2
    have Bmsubs : B1 \ {e} ⊆ B1 := by
      simp_all only [Finset.mem_sdiff, not_true, Finset.sdiff_subset]
    have Bmpow : B1 \ {e} ∈ Finset.powerset IMatroid.E := by
      simp only [Finset.mem_powerset]
      intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hb
      have hpow : B1 ∈ imat.E.powerset := imat.indPow hB1.left
      simp only [Finset.mem_powerset] at hpow
      exact hpow hb.left
    have Bmind : B1 \ {e} ∈ imat.ind :=
      imat.i2 B1 hB1.left (B1 \ {e}) Bmpow Bmsubs
    have Eq : #B1 = #B2 := ind_lem1 α imat B1 hB1' B2 hB2'
    have esub : {e} ⊆ B1 := by
      rename_i inst
      simp_all only [Finset.mem_sdiff, not_true, Finset.sdiff_subset,
      Finset.mem_powerset, Finset.singleton_subset_iff]
    have hCardge : #{e} ≤ #B1 := Finset.card_le_of_subset esub
    simp only [Finset.card_singleton] at hCardge
    have hcardlt : #(B1 \ {e}) < #B2 := calc
      #(B1 \ {e}) = #B1 - #{e} := Finset.card_sdiff esub
      _= #B1 - 1 := by simp only [Finset.card_singleton, ge_iff_le]
      _< #B1 - 1 + 1 := by
        simp only [ge_iff_le, Finset.card_eq_zero, lt_add_iff_pos_right]
      _= #B1 := Nat.sub_add_cancel hCardge
      _= #B2 := Eq
    have app := imat.i3 (B1 \ {e}) Bmind B2 hB2.left hcardlt
    apply Exists.elim app
    intro f hf
    apply Exists.intro f
    apply And.intro
    simp only [Finset.mem_sdiff]
    have hfr := hf.right
    have hfl := hf.left
    simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not] at hfl
    apply And.intro
    exact hfl.left
    intro fB1
    have hB1lj := hfl.right fB1
    simp only [Finset.mem_sdiff] at he
    apply he.right
    rw [hB1lj.symm]
    exact hfl.left
    simp only [Finset.mem_filter]
    apply And.intro
    exact hf.right
    intro I hI hBsubI
    have ex := ind_lem2 I hI
    apply Exists.elim ex
    intro B3 hB3
    have hB3r := hB3.right
    have hB3 := hB3.left
    have hCardEq : #B1 = #B3 := ind_lem1 α imat B1 hB1' B3 hB3
    have diffDisj : Disjoint (B1 \ {e}) {f} := by
      simp only [Finset.disjoint_singleton_right, Finset.mem_sdiff,
        Finset.mem_singleton, not_and, not_not]
      intro hfB1
      rename_i inst hB3_1
      simp_all only [Finset.mem_sdiff, Finset.mem_filter, true_and,
        not_true, Finset.sdiff_subset, Finset.mem_powerset,
        Finset.singleton_subset_iff, Finset.mem_singleton, not_and,
        not_not, Finset.sdiff_union_self_eq_union, and_true]
    have hCardDiffU : #(B1 \ {e} ∪ {f}) = #B1 := calc
      #(B1 \ {e} ∪ {f}) = #(B1 \ {e}) + #({f}) :=
        Finset.card_disjoint_union diffDisj
      _= #(B1 \ {e}) + 1 := by simp only [Finset.card_singleton]
      _= #(B1) - #({e}) + 1 :=
        by simp only [Finset.card_sdiff esub, Finset.card_singleton, ge_iff_le,
        Finset.card_eq_zero]
      _= #B1 - 1 + 1 :=
        by simp only [Finset.card_singleton, ge_iff_le, Finset.card_eq_zero]
      _= #B1 := Nat.sub_add_cancel hCardge
    rw [hCardDiffU.symm] at hCardEq
    have hBsubI := hBsubI
    have hbeep : #I ≤ #B3 := Finset.card_le_of_subset hB3r
    rw [hCardEq.symm] at hbeep
    exact Finset.eq_of_subset_of_card_le hBsubI hbeep

lemma r_i1 {α : Type} [DecidableEq α] (rmat : RMatroid α) :
  ∅ ∈ Finset.filter (fun I => RMatroid.rk I = #I) (rmat.E.powerset) := by
    simp only [Finset.mem_powerset, Finset.mem_filter]
    apply And.intro
    intro a ha
    apply False.elim
    rename_i inst
    simp_all only [Finset.not_mem_empty]
    rw [Finset.card_empty]
    have h1 : ∅ ∈ rmat.E.powerset := by
      simp only [Finset.mem_powerset, Finset.empty_subset]
    have h2 : RMatroid.rk ∅ ≤ #∅ := (RMatroid.r1 ∅) h1
    rename_i inst
    simp_all only [Finset.mem_powerset,
      Finset.empty_subset, Finset.card_empty, nonpos_iff_eq_zero]

lemma r_i2 {α : Type} [DecidableEq α] (rmat : RMatroid α) :
  ∀ (I2 : Finset α),
  I2 ∈ Finset.filter (fun I => RMatroid.rk I = #I) (Finset.powerset RMatroid.E) →
    ∀ (I1 : Finset α),
      I1 ∈ Finset.powerset RMatroid.E →
        I1 ⊆ I2 → I1 ∈ Finset.filter (fun I => RMatroid.rk I = #I) (Finset.powerset RMatroid.E) := by
    intro I1 hI1 I2 hI2 hSub
    simp only [Finset.mem_powerset, Finset.mem_filter]
    simp only [Finset.mem_powerset, Finset.mem_filter] at hI2
    simp only [Finset.mem_powerset, Finset.mem_filter] at hI1
    apply And.intro
    exact hI2
    have h1 : I1 ∈ RMatroid.E.powerset := by
      simp only [Finset.mem_powerset, hI1.left]
    have h2 : I2 ∈ RMatroid.E.powerset := by
      simp only [Finset.mem_powerset, hI2]
    exact rank_lem3 rmat I1 h1 I2 h2 hI1.right hSub

lemma r_i3 {α : Type} [DecidableEq α] (rmat : RMatroid α) :
  ∀ (I1 : Finset α),
  I1 ∈ Finset.filter (fun I => RMatroid.rk I = #I) (Finset.powerset RMatroid.E) →
    ∀ (I2 : Finset α),
      I2 ∈ Finset.filter (fun I => RMatroid.rk I = #I) (Finset.powerset RMatroid.E) →
        #I1 < #I2 →
          ∃ e, e ∈ I2 \ I1 ∧ I1 ∪ {e} ∈ Finset.filter (fun I => RMatroid.rk I = #I) (Finset.powerset RMatroid.E) := by
    intro I1 hI1 I2 hI2 hcard
    apply Or.elim (Classical.em
      (∃ e, e ∈ I2 \ I1 ∧ I1 ∪ {e} ∈ Finset.filter
      (fun I => RMatroid.rk I = #I)
      (Finset.powerset RMatroid.E)))
    intro h
    exact h
    intro contra
    apply False.elim
    have contra := forall_not_of_not_exists contra
    have hI1pow : I1 ∈ rmat.E.powerset := by
      simp only [Finset.mem_powerset, Finset.mem_filter] at hI1
      simp only [Finset.mem_powerset]
      exact hI1.left
    have hI2pow : I2 ∈ rmat.E.powerset := by
      simp only [Finset.mem_powerset, Finset.mem_filter] at hI2
      simp only [Finset.mem_powerset]
      exact hI2.left
    have Upow : I1 ∪ I2 ∈ Finset.powerset RMatroid.E := by
      simp only [Finset.mem_powerset]
      intro e
      simp only [Finset.mem_union]
      intro hor
      apply Or.elim hor
      intro heI1
      simp only [Finset.mem_powerset] at hI1pow
      apply hI1pow
      exact heI1
      intro heI2
      simp only [Finset.mem_powerset] at hI2pow
      apply hI2pow
      exact heI2
    have hBig :
      ∀ (e : α), e ∈ I1 ∪ I2 → RMatroid.rk I1 = RMatroid.rk (I1 ∪ {e}) := by
      intro e he
      apply Or.elim (Classical.em (e ∈ I1))
      intro heInI1
      have hesub : {e} ⊆ I1 := by
        simp only [Finset.singleton_subset_iff, heInI1]
      have hunion : I1 = I1 ∪ {e} := by
        rename_i inst contra_1
        simp_all only [Finset.mem_powerset, Finset.mem_filter, sdiff_self,
        Finset.bot_eq_empty, Finset.not_mem_empty,
        Finset.disjoint_singleton_right, false_and, exists_false, not_false_eq_true,
        implies_true, Finset.mem_union,
        true_or, Finset.singleton_subset_iff, Finset.left_eq_union_iff_subset]
      rw [hunion.symm]
      intro henInI1
      have heInI2 : e ∈ I2 := by
        rename_i inst contra_1
        simp_all only [Finset.mem_powerset, Finset.mem_filter,
          sdiff_self, Finset.bot_eq_empty, Finset.not_mem_empty,
          Finset.disjoint_singleton_right, false_and, exists_false,
          not_false_eq_true, implies_true, Finset.mem_union,
          false_or]
      have heInDiff : e ∈ I2 \ I1 := by
        simp only [Finset.mem_sdiff]
        apply And.intro heInI2 henInI1
      have hinE : e ∈ rmat.E := by
        simp only [Finset.mem_powerset] at hI2pow
        apply hI2pow
        exact heInI2
      have hr3 := RMatroid.r3 I1 hI1pow e hinE
      apply Or.elim (Classical.em (RMatroid.rk (I1 ∪ {e})  ≤ RMatroid.rk I1))
      intro hcase1
      exact Nat.le_antisymm hr3.left hcase1
      intro hcase2
      have hrk : RMatroid.rk (I1 ∪ {e}) = RMatroid.rk (I1) + 1 := by
        linarith
      have hcont := contra e
      apply False.elim
      apply hcont
      apply And.intro
      exact heInDiff
      have hdisj : Disjoint I1 {e} := by
        simp only [Finset.disjoint_singleton_right]
        exact henInI1
      have hcard2 : #(I1 ∪ {e}) = #(I1) + 1 := calc
        #(I1 ∪ {e}) = #I1 + #{e} := by
          simp only [Finset.disjoint_singleton_right, henInI1,
            not_false_eq_true, Finset.card_disjoint_union,
            Finset.card_singleton]
        _= #(I1) + 1 := by
          simp only [Finset.card_singleton]
      simp only [Finset.mem_powerset, Finset.mem_filter,
        Finset.disjoint_singleton_right]
      have hinSubs : I1 ∪ {e} ⊆ RMatroid.E := by
        intro f
        rename_i inst contra_1
        intro a
        simp_all only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_sdiff, Finset.disjoint_singleton_right, not_exists,
          not_and, not_false_eq_true, Finset.card_disjoint_union, Finset.card_singleton, and_imp, implies_true,
          Finset.mem_union, or_true, and_self, le_add_iff_nonneg_right, le_refl, add_le_iff_nonpos_right, and_true, true_and,
          Finset.mem_singleton]
        unhygienic with_reducible aesop_destruct_products
        unhygienic aesop_cases a
        · apply left
          simp_all only [not_false_eq_true]
        · aesop_subst h
          simp_all only [not_false_eq_true]
      apply And.intro
      exact hinSubs
      rw [hcard2, hrk]
      simp? at hI1
      rw [hI1.right]
    have subU : I1 ⊆ I1 ∪ I2 := Finset.subset_union_left I1 I2
    have hUnRk := rank_lem7 α rmat I1 hI1pow (I1 ∪ I2) Upow subU
    have contra := hUnRk hBig
    let n : ℕ := #(I1 ∪ I2) - #I2
    have hndef : n = #(I1 ∪ I2) - #I2 := by
      simp only [ge_iff_le]
    have hlem := rank_lem8 α rmat n I2 hI2pow (I1 ∪ I2) Upow
      (Finset.subset_union_right I1 I2) hndef.symm
    rw [contra.symm] at hlem
    simp only [Finset.mem_powerset, Finset.mem_filter] at hI1
    simp only [Finset.mem_powerset, Finset.mem_filter] at hI2
    rw [hI1.right] at hlem
    rw [hI2.right] at hlem
    linarith

lemma i_r1 {α : Type} [DecidableEq α] (imat : IMatroid α) :
  ∀ (A : Finset α),
  A ∈ Finset.powerset imat.E →
  (fun S => Finset.fold max 0 Finset.card (Finset.filter (fun I => I ⊆ S) IMatroid.ind)) A ≤ #A :=
  by
    intro A hA
    simp only
    let maxInd :=
      Finset.fold max 0 Finset.card (Finset.filter (fun I => I ⊆ A) IMatroid.ind)
    have leqS : maxInd ≤
      Finset.fold max 0 Finset.card (Finset.filter (fun I => I ⊆ A) IMatroid.ind) :=
      by simp only [le_refl]
    have hc := ((Finset.fold_max_le maxInd).mp leqS).right
    have hl := (Finset.le_fold_max maxInd).mp leqS
    apply Or.elim hl
    intro max0
    have m0 : maxInd = 0 := by linarith
    simp only at m0
    rw [m0]
    rename_i inst
    simp_all only [Finset.mem_powerset, le_refl, Finset.mem_filter, nonpos_iff_eq_zero,
      Finset.card_eq_zero, and_imp, zero_le, and_true, true_or]
    intro ex
    apply Exists.elim ex
    intro I hI
    have hIother := hc I hI.left
    have hEq : #I = maxInd := Nat.le_antisymm hIother hI.right
    simp only at hEq
    rw [hEq.symm]
    simp only [Finset.mem_filter, ge_iff_le] at hI
    exact Finset.card_le_of_subset hI.left.right

lemma i_c1 {α : Type} [DecidableEq α] (imat : IMatroid α) :
  ¬∅ ∈ Finset.filter (fun S => ¬S ∈ IMatroid.ind ∧ ∀ (e : α), e ∈ S → S \ {e} ∈ IMatroid.ind)
  (Finset.powerset IMatroid.E) := by
      intro hEmpt
      simp only [Finset.mem_powerset, Finset.mem_filter, Finset.empty_subset,
        Finset.not_mem_empty, not_false_eq_true,
        Finset.sdiff_singleton_eq_self, IsEmpty.forall_iff,
        implies_true, and_true, true_and] at hEmpt
      apply hEmpt
      exact imat.i1

lemma i_c2 {α : Type} [DecidableEq α] (imat : IMatroid α) :
  ∀ (C1 : Finset α),
  C1 ∈
      Finset.filter (fun S => ¬S ∈ IMatroid.ind ∧ ∀ (e : α), e ∈ S → S \ {e} ∈ IMatroid.ind)
        (Finset.powerset IMatroid.E) →
    ∀ (C2 : Finset α),
      C2 ∈ Finset.powerset IMatroid.E →
        C2 ⊂ C1 →
          ¬C2 ∈
              Finset.filter (fun S => ¬S ∈ IMatroid.ind ∧ ∀ (e : α), e ∈ S → S \ {e} ∈ IMatroid.ind)
                (Finset.powerset IMatroid.E) :=
  by
    intro C1 hC1 C2 hC2 hsubN
    have hsubs : C2 ⊆ C1 := (Finset.ssubset_iff_subset_ne.mp hsubN).left
    simp only [Finset.mem_powerset, Finset.mem_filter, not_and,
      not_forall, exists_prop]
    simp only [Finset.mem_powerset, Finset.mem_filter] at hC1
    intro C2subs hC2subs
    have hEx := Finset.exists_of_ssubset hsubN
    apply Exists.elim hEx
    intro e he
    apply False.elim
    have hsubs3 : C2 ⊆ C1 \ {e} := by
      intro c hc
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      apply And.intro
      apply hsubs
      exact hc
      intro cont
      rw [cont] at hc
      exact he.right hc
    have hmInd : C1 \ {e} ∈ imat.ind := hC1.right.right e he.left
    have hC2ind := imat.i2 (C1 \ {e}) hmInd C2 hC2 hsubs3
    exact hC2subs hC2ind

lemma c_i1 {α : Type} [DecidableEq α] (cmat : CMatroid α) :
  ∅ ∈ Finset.filter (fun S => ∀ (C : Finset α), C ∈ cmat.circ → ¬C ⊆ S) (Finset.powerset CMatroid.E) :=
  by
    simp only [Finset.mem_powerset, Finset.mem_filter,
      Finset.empty_subset, true_and]
    intro C hC f
    have f := Finset.subset_empty.mp f
    rw [f] at hC
    exact cmat.c1 hC

lemma c_i2 {α : Type} [DecidableEq α] (cmat : CMatroid α) :
  ∀ (I2 : Finset α),
  I2 ∈ Finset.filter (fun S => ∀ (C : Finset α), C ∈ CMatroid.circ → ¬C ⊆ S) (Finset.powerset CMatroid.E) →
    ∀ (I1 : Finset α),
      I1 ∈ Finset.powerset CMatroid.E →
        I1 ⊆ I2 →
          I1 ∈ Finset.filter (fun S => ∀ (C : Finset α), C ∈ CMatroid.circ → ¬C ⊆ S) (Finset.powerset CMatroid.E) :=
    by
      intro I2 hI2 I1 hI1 hsubs
      simp only [Finset.mem_powerset, Finset.mem_filter]
      apply And.intro
      rename_i inst
      simp_all only [Finset.mem_powerset, Finset.mem_filter]
      intro C hC hcont
      have htrans := Finset.Subset.trans hcont hsubs
      simp only [Finset.mem_powerset, Finset.mem_filter] at hI2
      exact (hI2.right C hC) htrans

lemma cl_h1 {α : Type} [DecidableEq α] (clmat : ClMatroid α) :
  ∀ (A1 : Finset α),
  A1 ∈ Finset.powerset ClMatroid.E →
    ∀ (A2 : Finset α),
      A2 ∈ Finset.powerset ClMatroid.E →
        A2 ⊂ A1 →
          ¬A1 ∈
                Finset.filter
                  (fun S =>
                    ClMatroid.cl S = S ∧
                      (∀ (e : α), e ∈ ClMatroid.E \ S → ClMatroid.cl (S ∪ {e}) = ClMatroid.E) ∧
                        ClMatroid.cl S ≠ ClMatroid.E)
                  (Finset.powerset ClMatroid.E) ∨
            ¬A2 ∈
                Finset.filter
                  (fun S =>
                    ClMatroid.cl S = S ∧
                      (∀ (e : α), e ∈ ClMatroid.E \ S → ClMatroid.cl (S ∪ {e}) = ClMatroid.E) ∧
                        ClMatroid.cl S ≠ ClMatroid.E)
                  (Finset.powerset ClMatroid.E) :=
    by
      intro A1 hA1 A2 hA2 hsubs
      have hsubs2 : A2 ⊆ A1 := (Finset.ssubset_iff_subset_ne.mp hsubs).left
      let hyp := Finset.filter
        (fun S =>
          ClMatroid.cl S = S ∧ (∀ (e : α),
          e ∈ ClMatroid.E \ S → ClMatroid.cl (S ∪ {e}) = ClMatroid.E) ∧
          clmat.cl S ≠ clmat.E)
        (Finset.powerset ClMatroid.E)
      have hypDef : hyp = Finset.filter
        (fun S =>
          ClMatroid.cl S = S ∧ (∀ (e : α),
          e ∈ ClMatroid.E \ S → ClMatroid.cl (S ∪ {e}) = ClMatroid.E) ∧
          clmat.cl S ≠ clmat.E)
        (clmat.E.powerset) := by rfl
      rw [hypDef.symm]
      apply Or.elim (Classical.em (A2 ∈ hyp))
      intro hA2hyp
      apply Or.inl
      simp only [Finset.mem_powerset, Finset.mem_sdiff, and_imp, true_and,
        Finset.mem_filter] at hA2hyp
      have hEx := Finset.exists_of_ssubset hsubs
      apply Exists.elim hEx
      intro e he
      have he2 : e ∈ ClMatroid.E := by
        simp only [Finset.mem_powerset] at hA1
        apply hA1
        exact he.left
      have hApp := hA2hyp.right.right.left e he2 he.right
      have hsubs3 : A2 ∪ {e} ⊆ A1 := by
        intro f hf
        simp only [Finset.mem_union, Finset.mem_singleton] at hf
        apply Or.elim hf
        intro hfA2
        apply hsubs2
        exact hfA2
        intro hfe
        rename_i inst
        aesop_subst hfe
        simp_all only [Finset.mem_powerset, Finset.mem_sdiff, and_imp,
          true_and, not_false_eq_true, or_true]
      have hclosure := clmat.cl3 (A2 ∪ {e}) A1 hsubs3
      rw [hApp] at hclosure
      have hEPow : clmat.E ∈ clmat.E.powerset :=
        by simp only [Finset.mem_powerset, Finset.Subset.refl]
      have hE := clmat.cl1 clmat.E hEPow
      have hK := clmat.clPow A1 hA1
      simp only [Finset.mem_powerset] at hK
      have hEq2 : ClMatroid.cl A1 = clmat.E :=
      Finset.Subset.antisymm hK hclosure
      simp only [Finset.mem_filter]
      intro cont
      exact cont.right.right.right hEq2
      intro hnA2hyp
      apply Or.inr hnA2hyp

lemma h_cl1 {α : Type} [DecidableEq α] (hmat : HMatroid α) :
  ∀ (A : Finset α),
  A ∈ Finset.powerset HMatroid.E →
    A ⊆ (fun S => Finset.filter (fun e => ∀ (H : Finset α), H ∈ HMatroid.hyp → S ⊆ H → e ∈ H) HMatroid.E) A := by
      intro S hS e he
      simp only [Finset.mem_filter]
      apply And.intro
      simp only [Finset.mem_powerset] at hS
      exact hS he
      intro H hH hsubs
      exact hsubs he

lemma h_cl2 {α : Type} [DecidableEq α] (hmat : HMatroid α) :
  ((fun S => Finset.filter (fun e => ∀ (H : Finset α), H ∈ HMatroid.hyp → S ⊆ H → e ∈ H) HMatroid.E) ∘ fun S =>
    Finset.filter (fun e => ∀ (H : Finset α), H ∈ HMatroid.hyp → S ⊆ H → e ∈ H) HMatroid.E) =
  fun S => Finset.filter (fun e => ∀ (H : Finset α), H ∈ HMatroid.hyp → S ⊆ H → e ∈ H) HMatroid.E := by
      apply Function.funext_iff.mpr
      intro S
      apply Finset.Subset.antisymm
      intro a ha
      simp only [Function.comp_apply, Finset.mem_filter] at ha
      simp only [Finset.mem_filter]
      apply And.intro
      exact ha.left
      intro H hH hSH
      have ha1 := ha.right H hH
      apply ha1
      intro e he
      simp only [Finset.mem_filter] at he
      apply he.right H hH hSH
      intro a ha
      simp only [Function.comp_apply, Finset.mem_filter]
      apply And.intro
      rename_i inst
      simp_all only [Finset.mem_filter]
      intro H1 hH1 hSub
      apply hSub
      simp only [Finset.mem_filter]
      apply And.intro
      rename_i inst
      simp_all only [Finset.mem_filter]
      intro H2 hH2 hSub2
      simp only [Finset.mem_filter] at ha
      apply ha.right H2 hH2 hSub2

lemma h_cl3 {α : Type} [DecidableEq α] (hmat : HMatroid α) :
  ∀ (A B : Finset α),
  A ⊆ B →
    (fun S => Finset.filter (fun e => ∀ (H : Finset α), H ∈ HMatroid.hyp → S ⊆ H → e ∈ H) HMatroid.E) A ⊆
      (fun S => Finset.filter (fun e => ∀ (H : Finset α), H ∈ HMatroid.hyp → S ⊆ H → e ∈ H) HMatroid.E) B := by
      intro A B hSub
      intro a hA
      simp only [Finset.mem_filter]
      apply And.intro
      rename_i inst
      simp_all only [Finset.mem_filter]
      intro H hH hsub2
      simp only [Finset.mem_filter] at hA
      have hkl := hA.right H hH
      apply hkl
      exact Finset.Subset.trans hSub hsub2

lemma cl_i1 {α : Type} [DecidableEq α] (clmat : ClMatroid α) :
  ∅ ∈ Finset.filter (fun S => ∀ (e : α), e ∈ S → ClMatroid.cl S ≠ ClMatroid.cl (S \ {e})) (Finset.powerset ClMatroid.E) := by
      simp only [ne_eq, Finset.mem_powerset, Finset.mem_filter,
        Finset.empty_subset, Finset.not_mem_empty,
        not_false_eq_true, Finset.sdiff_singleton_eq_self,
        not_true, IsEmpty.forall_iff, implies_true, and_self]
