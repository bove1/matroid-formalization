import MatroidFormalization.Lemmas

/-
  This file contains the definitions for conversions. Most proofs, if not
  sorried out, have been moved to the lemmas file. We have a "complete set"
  of conversion here, in the sense that any conversion from one definition
  to another can be made by composition compositions here. Here's a little
  commutative diagram of this.

       C
       ↕
   B ↔ I ↔ R
   ↓   ↑
   H ↔ Cl
-/

def R_to_I_conv (α : Type) [DecidableEq α] : RMatroid α → IMatroid α :=
  fun rmat ↦ {
    E     := rmat.E
    ind   := -- Independent sets are those with rank equal to size
      Finset.filter (fun I : Finset α ↦ rmat.rk I = #I) rmat.E.powerset
    indPow:= by
      simp only [Finset.mem_powerset, Finset.filter_subset]
    i1    := r_i1 rmat
    i2    := r_i2 rmat
    i3    := r_i3 rmat
  }

def I_to_B_conv (α : Type) [DecidableEq α] : IMatroid α → BMatroid α :=
  fun imat ↦ {
    E       := imat.E
    basis   := -- Maximally independent sets form basis
      Finset.filter (fun I1 ↦ ∀ I2 ∈ imat.ind, I1 ⊆ I2 → I1 = I2) imat.ind
    basisPow := by
      intro I1 hI1
      simp only [Finset.mem_filter] at hI1
      exact imat.indPow hI1.left
    b1      := i_b1 imat
    b2      := i_b2 imat
  }

def B_to_I_conv (α : Type) [DecidableEq α] : BMatroid α → IMatroid α :=
  fun bmat ↦ {
    E := bmat.E
    ind := -- Subsets of basis are independent.
      Finset.filter (fun I ↦ ∃B ∈ bmat.basis, I ⊆ B) bmat.E.powerset
    indPow := by
      intro B1 hB1
      rename_i inst
      simp_all only [Finset.mem_powerset, Finset.mem_filter]
    i1 := b_i1 bmat
    i2 := b_i2 bmat
    i3 := b_i3 bmat
  }

/-
  My proof of b_i3 became a massive mess (and still isn't finished). In
  general, it seems the proofs involving the "exchange axioms" in one form
  or another are the most difficult to work with, as they usually require
  some form of a creative induction. Thus, I'm going to state the remainder
  of the conversions and only proving the other axioms.
-/

def I_to_R_conv {α : Type} [DecidableEq α] : IMatroid α → RMatroid α :=
  fun imat ↦ {
    E := imat.E
    rk := -- Set S has rank equal to size of maximal independent subset.
      fun S ↦ Finset.fold max 0 Finset.card
        (Finset.filter (fun I ↦ I ⊆ S) imat.ind)
    r1 := i_r1 imat
    r2 := sorry
    r3 := sorry
  }

def I_to_C_conv {α : Type} [DecidableEq α] : IMatroid α → CMatroid α :=
  fun imat ↦ {
    E := imat.E
    circ := -- Circuits are minimally dependent sets
      Finset.filter
      (fun S ↦ S ∉ imat.ind ∧ ∀e ∈ S, S \ {e} ∈ imat.ind)
      imat.E.powerset
    circPow := by
      intro I hI
      simp only [Finset.mem_powerset, Finset.mem_filter] at hI
      simp only [Finset.mem_powerset]
      exact hI.left
    c1 := i_c1 imat
    c2 := i_c2 imat
    c3 := sorry
  }

def C_to_I_conv {α : Type} [DecidableEq α] : CMatroid α → IMatroid α :=
  fun cmat ↦ {
    E := cmat.E
    ind := -- Independet sets are those not containing a circuit
      Finset.filter
      (fun S ↦ ∀ C ∈ cmat.circ, ¬ C ⊆ S)
      cmat.E.powerset
    indPow := by
      intro I hI
      simp only [Finset.mem_powerset, Finset.mem_filter] at hI
      simp only [Finset.mem_powerset]
      exact hI.left
    i1 := c_i1 cmat
    i2 := c_i2 cmat
    i3 := sorry
  }

/-
  The hardest conversions, as we'll see in a second, are those involving
  either the closure or hyperplane definition. Converting between the two
  is relatively easy, but converting to and from is more difficult. First,
  we look at conversions between the two:
-/

def Cl_to_H_conv {α : Type} [DecidableEq α] : ClMatroid α → HMatroid α :=
  fun clmat ↦ {
    E := clmat.E
    hyp := -- Hyperplanes are sets that are equal to their closure,
      -- and adding any additional element will make the closure all of E.
      Finset.filter
      (fun S ↦ clmat.cl S = S ∧
        (∀e ∈ clmat.E \ S, clmat.cl (S ∪ {e}) = clmat.E) ∧
        clmat.cl S ≠ clmat.E)
      clmat.E.powerset
    hypPow := by
      intro I hI
      simp only [Finset.mem_powerset, Finset.mem_filter] at hI
      simp only [Finset.mem_powerset]
      exact hI.left
    h1 := cl_h1 clmat
    h2 := sorry
  }

def H_to_Cl_conv {α : Type} [DecidableEq α] : HMatroid α → ClMatroid α :=
  fun hmat ↦ {
    E := hmat.E
    cl := -- An element is in the closure of S iff it is in the
    -- intersection of all hyperplanes containing S.
      fun S ↦ Finset.filter
      (fun e ↦ ∀H ∈ hmat.hyp, S ⊆ H → e ∈ H) hmat.E
    clPow := by
      intro S hS
      simp only [Finset.mem_powerset, Finset.filter_subset]
    cl1 := h_cl1 hmat
    cl2 := h_cl2 hmat
    cl3 := h_cl3 hmat
    cl4 := sorry
  }

#check Function.funext_iff

/-
  The simplest way to get from these two to our previous definition is
  defining independent sets in terms of the closure operator.
-/

def Cl_to_I_conv {α: Type} [DecidableEq α] : ClMatroid α → IMatroid α :=
  fun clmat ↦ {
    E := clmat.E
    ind := -- Independent sets are those whose closures contain more elements
           -- than the closure of any proper subset.
      Finset.filter
      (fun S ↦ ∀e ∈ S, clmat.cl S ≠ clmat.cl (S \ {e}))
      clmat.E.powerset
    indPow := by
      simp only [ne_eq, Finset.mem_powerset, Finset.filter_subset]
    i1 := cl_i1 clmat
    i2 := sorry
    i3 := sorry
  }

/-
  To convert to the hyperplane definition (and thus also to the closure
  operator), we'll need to get creative. The following conversion took some
  hard thinking, and I'm not actually sure if I got it right.
-/

def B_to_H_conv {α : Type} [DecidableEq α] : BMatroid α → HMatroid α :=
  fun bmat ↦ {
    E := bmat.E
    hyp := -- Hyperplanes do not contain a basis, but any larger set
      -- does.
      Finset.filter (fun S ↦
        (∀B ∈ bmat.basis, ¬B ⊆ S) ∧
        (∀e ∈ bmat.E \ S, ∃B ∈ bmat.basis, B ⊆ S ∪ {e}))
      bmat.E.powerset
    hypPow := by
      intro I hI
      simp only [Finset.mem_powerset, Finset.mem_filter] at hI
      simp only [Finset.mem_powerset]
      exact hI.left
    h1 := sorry
    h2 := sorry
  }
