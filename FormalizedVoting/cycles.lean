-- old import
-- import tactic
-- import data.list.chain
-- import data.fintype.basic
-- import data.list.rotate
-- import data.list.basic
-- import tactic.omega
-- import data.nat.modeq
-- import tactic.zify
-- import data.stream.basic

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Mathlib.Data.Nat.ModEq
import Mathlib.Logic.Relation


open Classical
noncomputable section

variable {X : Type u}

/- -------------------- Basic defs -------------------- -/

def cycle (P : X → X → Prop) (c : List X) : Prop :=
  ∃ h : c ≠ [], List.IsChain P ((c.getLast h) :: c)

def reverse (P : X → X → Prop) (x y : X) : Prop := P y x

/-- If `c` is a cycle, then the list `l` is nonempty. -/
lemma length_cycle_pos {l : List X} {P : X → X → Prop} (c : cycle P l) : 0 < l.length := by
  rcases c with ⟨hne, _⟩
  exact List.length_pos_iff_ne_nil.mpr hne

def acyclic (P : X → X → Prop) : Prop :=   ∀ c : List X, ¬ cycle P c


/- -------------------- List helpers -------------------- -/

-- lemma nth_reverse
#check List.getElem_reverse

-- Nonempty reverse if original has positive length
lemma nonempty_last (l : List X) (e : l.length > 0) : l.reverse ≠ [] := by
  have : (l.reverse).length = l.length := by simp
  exact List.ne_nil_of_length_pos (by omega)

-- The get version, in case needed.
-- Identify last element of reverse with head of original
-- lemma last_reverse (l : List X) (e : l.length > 0) :
--     l.reverse.getLast (nonempty_last l e) = l.get ⟨0, e⟩ := by
--   rw [List.getLast_eq_getElem]
--   simp only [List.getElem_reverse, List.length_reverse]
--   congr 1
--   omega
#check List.getLast_reverse


/- -------------------- Stream' helpers -------------------- -/

-- lemma length_take
#check Stream'.length_take

-- -- The get version of nth_take, nth_take_get, in case needed.
-- lemma nth_take_get_ineq {a b c : ℕ} (d : a < b) (e : c = b) : a < c := by omega

-- /-- For any stream `s`, the `i`-th element of `take n s` (when `i < n`)
--     is exactly `s i`. -/
-- lemma nth_take_get {X : Type} {n i : ℕ} (e : i < n) (s : Stream' X) :
-- ((s.take n).get ⟨ i, (nth_take_get_ineq e (s.length_take n))⟩ )=(s i):= by
--   simp [Stream'.get]

@[simp]
lemma nth_take {X : Type} {n i : ℕ} (e : i < n) (s : Stream' X) :
(s.take n)[i]'(by rw [Stream'.length_take]; exact e) = (s i):= by
  simp [Stream'.get]
