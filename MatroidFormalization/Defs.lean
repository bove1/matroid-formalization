import MatroidFormalization.MatroidLib

prefix:75  "#"   => Finset.card

/-
This file contains the most common definitions used in matroid theory.

Before reading, I'll briefly describe the mathematical idea behind a
matroid. Matroids are intended to "generalize linear independence."
They consist of a finite set, the elements of which are traditionally
called "edges" (more on this term later). The best analogy for these
elements is the columns of a matrix in some vector space. The matroid
stores the "data" of what combinations of columns are/aren't linearly
independent.

There are a few properties we expect linearly independent vectors
to have. For one, if a set is linearly independent, so should be any
subset. Second, the empty set should be linearly independent. The
final property is the most difficult but also the most fruitful,
what makes matroids so interesting.

In linear algebra terms:

Suppose you have two linearly independent sets of vectors I1 and I2
where I2 is larger than I1. It follows that dim(span(I2)) >
dim(span(I1)). Suppose now to the contrary that span(I1) contains
all of I2. This would mean that I2 fits in a space with smaller
dimension that #I2. But this would imply that I2 is linearly
dependent. Thus, there is some vector in I2 not in the span of I1,
and so we can extend I1 to the linearly independent set I1 ∪ {e}.

More combinatorically: Suppose I1, I2 independent with #I2 > #I1,
∃e ∈ I2 \ I1 such that I1 ∪ {e} indepenent.

This is known as the "exchange axiom", and you will find that all
formulations of a matroid have some glaringly obvious analogue of it.
In general, the exchange axiom is the most difficult part of dealing
with matroids, but also the *key ingredient* for combinatorially
generalizing many results on linear independence. I'll briefly explain
what concept each of the following definitions is generalizing, and
point out which axiom in their definition is the analogue of the exchange
property.

Before this, though, I'll point out one more context in which matroids
arise: Graph theory. Given a graph G, we can define a matroid on the
edges of G (where this terminology originates), where independent sets
are those that do not contain cycles. I'll leave it to the reader to
confirm the independence axioms for this property.
-/

class IMatroid (α : Type) [DecidableEq α]  where
  E       : Finset α
  ind     : Finset (Finset α)
  indPow  : ind ⊆ E.powerset
  i1      : ∅ ∈ ind
  i2      : ∀I2 ∈ ind, ∀I1 ∈ E.powerset,
            I1 ⊆ I2 → I1 ∈ ind
          -- Exchange property
  i3      : ∀I1 ∈ ind, ∀I2 ∈ ind,
             #I1 < #I2 →
             ∃e ∈ I2 \ I1, I1 ∪ {e} ∈ ind

/-
The Basis Definition of a matriod generalizes two things:
 - Spanning trees of a graph (spanning forest in the disconnected
  case) and
 - Bases of a vector space.
More precisely, the basis definition defines independent sets
using only the set of maximal independent sets. One nonobvious
implication of the basis definition is that all bases have the
same cardinality, which is proven in the "Lemmas" file with some
heavy duty induction.
-/

class BMatroid (α : Type) [DecidableEq α] where
  E         : Finset α
  basis     : Finset (Finset α)
  basisPow  : basis ⊆ E.powerset
  b1        : basis ≠ ∅
            -- Exchange property
  b2        : ∀B1 ∈ basis, ∀B2 ∈ basis, ∀e ∈ (B1 \ B2),
              ∃f ∈ (B2 \ B1), (B1 \ {e}) ∪ {f} ∈ basis

/-
The Circuit definition of a matroid best corresponds to the idea
of a "cycle" in a graph. Clearly, the set of cycles in a graph
carry the information of acyclic sets, and thus independent sets.
Stated more combinatorically, the circuits of a matroid are the
minimally dependent sets.
-/

class CMatroid (α : Type) [DecidableEq α]where
  E       : Finset α
  circ    : Finset (Finset α)
  circPow : circ ⊆ E.powerset
  c1      : ∅ ∉ circ
  c2      : ∀C1 ∈ circ, ∀C2 ∈ E.powerset,
          C2 ⊂ C1 → C2 ∉ circ
          -- Exchange property
  c3      : ∀C1 ∈ circ, ∀C2 : circ, C1 ≠ C2 →
          ∃e ∈ C1 ∩ C2, ∃C3 ∈ circ, C3 ⊆ (C1 ∪ C2) \ {e}

/-
The Rank definition, unlike the previous three, does not
define a matroid using a set of subsets, but rather by
associating a "rank" to each subset of the edge set. This
corresponds to the dimension of the span of a set of vectors
in the linear algebra context.
-/

class RMatroid (α : Type) [DecidableEq α] where
  E     : Finset α
  rk    : Finset α → ℕ
  r1    : ∀A ∈ E.powerset, rk A ≤ #A
  r2    : ∀A ∈ E.powerset, ∀ B ∈ E.powerset,
          rk (A ∪ B) + rk (A ∩ B) ≤ rk A + rk B
        -- Exchange property
  r3    : ∀A ∈ E.powerset, ∀e ∈  E,
          rk A ≤ rk (A ∪ {e}) ∧ rk (A ∪ {e}) ≤ rk A + 1

/-
The Closure definition is a bit more subtle. It maps every
set to its "closure." In the context of vector spaces, this
takes a subset of a matroid to the set of vectors in the span
of that set. As with most closure operators, this map is
idempotent, along with having its own version of the exchange
axiom.
-/

class ClMatroid (α : Type) [DecidableEq α] where
  E     : Finset α
  cl    : Finset α → Finset α
  clPow : ∀A ∈ E.powerset, cl A ∈ E.powerset
  cl1   : ∀A ∈ E.powerset, A ⊆ (cl A)
  cl2   : cl ∘ cl = cl
  cl3   : ∀A B: Finset α, A ⊆ B → cl A ⊆ cl B
        -- Exchange property.
  cl4   : ∀e ∈ E, ∀ f ∈ E, ∀A ∈ E.powerset,
          e ∈ cl (A ∪ {f}) \ cl A → f ∈ cl (A ∪ {e}) \ cl A

/-
We can also store the information of the "hyperplanes" of M,
or maximal sets of vectors spanning some dim(V) - 1 dimensional
space. This definition is difficult to work with and not
used very often.
-/
class HMatroid (α : Type) [DecidableEq α] where
  E     : Finset α
  hyp   : Finset (Finset α)
  hypPow : hyp ⊆ E.powerset
  h1    : ∀A1 ∈ E.powerset, ∀A2 ∈ E.powerset, A2 ⊂ A1 →
          (A1 ∉ hyp ∨ A2 ∉ hyp)
  h2    : ∀e ∈ E, ∀H1 ∈ hyp, ∀H2 ∈ hyp, H1 ≠ H2 →
          e ∉ H1 ∪ H2 → ∃H3 ∈ hyp, (H1 ∩ H2) ∪ {e} ⊆ H3
