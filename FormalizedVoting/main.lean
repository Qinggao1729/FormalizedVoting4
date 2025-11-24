import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.toNat
import Mathlib.Tactic.Basic

import FormalizedVoting.Cycles

open Classical
set_option autoImplicit true
noncomputable section

/-- Definition 1: **Prof V X** represents the set of `(V, X)`-profiles,
where a profile is a per-voter preference relation on `X`. -/
def Prof (V X : Type) : Type := V → X → X → Prop

/-- Definition 2: Given a profile `P` and `x`, `y` ∈ `X(P)`,
we say that `x` is **majority preferred** to `y` in `P` if
more voters rank `x` above `y` than rank `y` above `x`. -/
def majority_preferred {V X : Type} (P : Prof V X) (x y : X) : Prop :=
  Cardinal.mk {v : V // P v x y} > Cardinal.mk {v : V // P v y x}

/-- Definition 3: Given a profile P and x₁, x₂ ∈ X(P),
the **margin** of `x₁` over `x₂` in `P`, denoted `Marginₚ(x₁, x₂)`, is
`|{i ∈ V (P) | x₁Pᵢx₂}| − |{i ∈ V (P) | x₂Pᵢx₁}|`. -/
def margin {V X : Type} [Fintype V] (P : Prof V X) (x₁ x₂ : X) : ℤ :=
  (Cardinal.toNat (Cardinal.mk {v : V // P v x₁ x₂}) : ℤ)
  - (Cardinal.toNat (Cardinal.mk {v : V // P v x₂ x₁}) : ℤ)

/-- Definition: The property of skew-symmetry takes in a function
and outputs the proposition stating that the
**skew-symmetry** equation `M x y = - M y x` holds for all pairs `x`, `y`. -/
def skew_symmetric {X : Type} (M : X → X → ℤ) : Prop :=
  ∀ x y, M x y = - M y x

/-- Margin is skew-symmetric for any profile `P`. -/
lemma margin_skew_symmetric {V X : Type} (P : Prof V X) [Fintype V] :
    skew_symmetric (margin P) := by
  intro x y
  simp [margin]

/-- Definition: We say that `x` is a **majority winner** in `P` if the number of voters
who rank `x` (and only `x`) in first place is greater than the number
of voters who do not rank `x` in first place. -/
def majority_winner {V X : Type} (P : Prof V X) (x : X) : Prop :=
  Cardinal.mk {v : V // ∀ y, y ≠ x → P v x y}
    > Cardinal.mk {v : V // ∃ y, y ≠ x ∧ P v y x}

/-- Definition 5: Let `SCC` be a function that assigns
to each pair `(V, X)` the set of all `(V, X)`-SCCs. -/
def SCC (V X : Type) : Type := Prof V X → Set X

/-- Definition: An SCC has universal domain if
the SCC outputs a non-empty set for all profiles. -/
def universal_domain_SCC {V X : Type} (F : SCC V X) : Prop :=
  ∀ P : Prof V X, F P ≠ ∅

/-- Definition 6: A variable-election social choice correspondence (VSCC)
is a function `F` that assigns to each pair `(V, X)` a `(V,X)`-SCC. -/
def VSCC : Type 1 := (V X : Type) → SCC V X

def finite_universal_domain_VSCC (F : VSCC) : Prop :=
  ∀ (V X : Type) [Inhabited V] [Inhabited X] [Fintype V] [Fintype X],
    universal_domain_SCC (F V X)

/-- A collective choice rule for `(V, X)`, or `(V, X)`-CCR, is
a function `f : Prof(V, X) → B(X)`. Let `CCR` be a function
that assigns to each pair `(V, X)` of the set of all `(V,X)`-CCRs. -/
def CCR (V X : Type) : Type := Prof V X → X → X → Prop

/-- Definition 8: A variable-election collective choice rule (VCCR)
is a function that assigns to each pair `(V, X)` a `(V, X)`-CCR. -/
def VCCR : Type 1 := (V X : Type) → CCR V X

/-- Definition 9: Given an asymmetric VCCR `F`, we define the induced VSCC `F*`
such that for any `V`, `X`, and `(V, X)`-profile `P`, we have
`F*(V,X)(P) = {x ∈ X(P) | ∀y ∈ X(P), (y, x) ∉ F(V, X)(P)}`.

Intuitively, there must exist an element `x` that is not beaten by any `y` in `F(V, X)(P)`. -/
def max_el_VSCC (f : VCCR) : VSCC := fun V X P => {x | ∀ y : X, ¬ f V X P y x}

lemma max_el_VSCC_ineq {first second : ℕ} : first < second → (second - 1).succ = second := by omega
lemma max_el_VSCC_ineq2 (first second i : ℕ) :
  i + 1 < second - first →
  (first + (second - first - 1 - (i + 1))).succ = (first + (second - first - 1 - i)) := by
  omega

/-- Acyclic + finite set + infinite walk (`∀ n, seq n ← seq (n+1)`) ⇒ contradiction (cycle appears).

For finite set of vertices (`X`) ⇒ any infinite walk has two repeating positions (`seq i = seq j`).
Then edges `seq i ← seq (i+1) ← … ← seq (j-1)` form a cycle if assuming an infinite walk. -/
lemma false_of_sequence_acyclic_vccr
    {V X : Type} [Fintype X] {F : VCCR} {P : Prof V X}
    (hacyclic : acyclic (F V X P))
    (seq : Stream' X)
    (property : ∀ n : ℕ, F V X P (seq (n.succ)) (seq n)) : -- an infinite walk through the vertices
    False := by
    have h_not_inj : ¬ Function.Injective seq := not_injective_infinite_finite seq
    simp only [Function.Injective] at h_not_inj
    push_neg at h_not_inj
    rcases h_not_inj with ⟨first, second, h_eq, ne⟩

    wlog h : first < second generalizing first second
    -- Suppose the lemma holds for first < second.
    -- Show that it holds for ¬ (first < second) too.
    · have h' : second < first := by omega
      exact this second first h_eq.symm ne.symm h'

    let l := (List.drop first (seq.take second)).reverse
    -- l = [seq (second-1), ... seq (first+1), seq first]
    have not_acyclic : ¬ acyclic (F V X P):= by
      unfold acyclic
      push_neg
      use l
      have e : l ≠ List.nil := by
        refine List.ne_nil_of_length_pos ?_
        rw [List.length_reverse, List.length_drop, Stream'.length_take]
        omega
      use e
      apply List.isChain_cons.mpr
      refine And.intro ?firstEdge ?restChain

      -- firstEdge: ∀ y ∈ l.head?, F V X P (l.getLast e) y
      · intro y hy
        rcases List.exists_cons_of_ne_nil e with ⟨x, xs, hxs⟩
        simp [hxs] at hy

        have eq1 : (l.getLast e) = seq second:= by
          rw [← h_eq]
          -- l = [seq (second-1), ... seq (first+1), seq first]
          rw [List.getLast_reverse, List.head_drop]
          have hnt := nth_take (n := second) (i := first) h seq
          simpa [Stream'.length_take] using hnt
        rw [eq1]

        have eq2: y = seq (second - 1) := by
          rw [← hy]
          have h_idx : x = l[0]'(List.length_pos_of_ne_nil e) := by simp [hxs]
          rw [h_idx]
          rw [List.getElem_reverse]
          -- simp [List.length_drop, Stream'.length_take, List.getElem_drop]
          simp [Stream'.get]
          congr 1
          omega
        rw [eq2]

        -- replace ∀ n by n = second - 1 in property
        specialize property (second - 1)
        rw [max_el_VSCC_ineq h] at property
        exact property

      -- restChain: List.IsChain (F V X P) l
      · refine List.isChain_iff_get.mpr ?_
        intro i h_i
        simp only [l, List.get_eq_getElem]
        simp [Stream'.get, List.getElem_reverse, List.getElem_drop]
        simp [l] at h_i
        rw [← max_el_VSCC_ineq2 first second i h_i]
        apply property

    exact not_acyclic hacyclic

/-- Nonemptiness of the `max_el_VSCC` choice set under acyclicity.

Assume by contradiction that every element is beaten by someone (`∀ x, ∃ y, F V X P y x`).
Then construct an infinite walk.
Then by the previous lemma, acyclic + finite set + infinite walk ⇒ contradiction (cycle appears). -/
theorem max_el_VSCC_defined
    {V X : Type} (F : VCCR) (P : Prof V X)
    (hacyc : acyclic (F V X P))
    [Inhabited X] [Fintype X] :
    (max_el_VSCC F V X P).Nonempty := by
  rw [Set.Nonempty]
  by_contra h
  simp only [max_el_VSCC, Set.mem_setOf_eq] at h
  push_neg at h

  let defeater (x : X) : X := Classical.choose (h x)
  -- Construct the infinite stream by starting at `default` and keep applying `next_better`
  -- You only know that the `default` is some element of `X` ([Inhabited X])
  let seq : Stream' X := Stream'.iterate defeater default
  -- Prove the stream respects the relation F
  have property (n : ℕ) : F V X P (seq n.succ) (seq n) := by
    simp only [seq]
    simp only [Stream'.iterate]
    -- Prove that this choice is valid by choosing the defeater of the current element
    -- #check Classical.choose_spec (h (seq n))
    -- choose_spec (h (seq n)) : F V X P (choose (h (seq n))) (seq n)
    exact Classical.choose_spec (h (seq n))

  exact false_of_sequence_acyclic_vccr hacyc seq property

/-- Any acyclic VCCR induces a VSCC with (finite) universal domain. -/
theorem max_el_VSCC_universal_domain
    (F : VCCR)
    (a : ∀ (V X : Type) [Inhabited V] [Inhabited X] [Fintype V] [Fintype X]
            (P : Prof V X), acyclic (F V X P)) :
    finite_universal_domain_VSCC (max_el_VSCC F) := by
  intro V X _ _ _ _ P
  rw [Set.nonempty_iff_ne_empty.symm]
  exact max_el_VSCC_defined F P (a V X P)


variable {V X : Type}

def asymmetric (Q : X → X → Prop) : Prop :=
  -- Don't try to infer x and y until the implication Q x y is provided.
  -- Usually used in logical predicates. This prevents tactics like apply from failing.
  ∀ ⦃x y⦄, Q x y → ¬ Q y x

class ProfileIrreflexive (P : Prof V X) where
  irreflexive : ∀ v, Irreflexive (P v)

class ProfileAsymmetric (P : Prof V X) where
  asymmetric : ∀ v, asymmetric (P v)

class ProfileTransitive (P : Prof V X) where
  transitive : ∀ v, Transitive (P v)

class ProfileTrichotomous (P : Prof V X) where
  trichotomous : ∀ v a b, P v a b ∨ a = b ∨ P v b a

/-- Asymmetric ⇒ Irreflexive -/
instance irreflexive_of_asymmetric {V X : Type} (P : Prof V X) [ProfileAsymmetric P] :
    ProfileIrreflexive P where
  irreflexive := fun v x h_ref => show False by
    exact (ProfileAsymmetric.asymmetric v) h_ref h_ref

def antisymmetric : (X → X → ℤ) → Prop := fun P => ∀ x y, P x y = - P y x

lemma margin_antisymmetric (P : Prof V X) [Fintype V] : antisymmetric (margin P) := by
    unfold margin
    intro x y
    simp

def margin_pos [Fintype V] : Prof V X → X → X → Prop := fun P x y => 0 < (margin P) x y

lemma margin_eq_margin (ft1 ft2 : Fintype V) (P : Prof V X) (x y : X) :
    @margin V X ft1 P x y = @margin V X ft2 P x y := by
  -- Congruence logic: "If the arguments are equal, the results are equal"
  -- A Fintype instance provides a Finset (a finite set) containing all elements of V.
  -- Then two instances of Fintype V must be equal because they both represent the same finite set.
  congr

lemma self_margin_zero [Fintype V] (x : X) (P : Prof V X) : margin P x x = 0 := by
    unfold margin
    simp

lemma ne_of_margin_pos [Fintype V] {P : Prof V X} {x y : X} (hpos : margin_pos P x y) : x ≠ y := by
    by_contra h_eq
    subst h_eq
    unfold margin_pos at hpos
    rw [self_margin_zero] at hpos
    simp at hpos
