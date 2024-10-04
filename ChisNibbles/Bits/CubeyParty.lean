import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-
216 is the least natural number which is the sum of distinct cubes in
at least two different ways.

Proof: it's decidable.
-/


-- TODO: try having parts be a Finset ℕ+ instead. I think it's actually worse?
structure CubeyParty (n : ℕ) where
  parts : Finset ℕ
  parts_pos : ∀ p ∈ parts, 0 < p
  sum_parts : ∑ p ∈ parts, p ^ 3 = n

namespace CubeyParty

open Finset

@[ext] structure UpTo (n k : ℕ) where
  parts : Finset ℕ
  parts_bdd : ∀ p ∈ parts, 0 < p ∧ p ≤ k
  sum_parts : ∑ p ∈ parts, p ^ 3 = n

namespace UpTo

def zero : UpTo 0 0 where
  parts := {}
  parts_bdd := by simp
  sum_parts := by simp

def cons {n k} v (h : k < v) (a : UpTo n k) : UpTo (n + v ^ 3) v where
  parts := a.parts.cons v fun hv => a.parts_bdd _ hv |>.2.not_lt h
  parts_bdd p := by
    rw [mem_cons]
    rintro (rfl | hp)
    . omega
    . exact a.parts_bdd _ hp |>.imp_right h.le.trans'
  sum_parts := by rw [sum_cons, a.sum_parts, add_comm]

def inclLe {n k} {k'} (h : k ≤ k') (a : UpTo n k) : UpTo n k' where
  __ := a
  parts_bdd p hp := a.parts_bdd p hp |>.imp_right h.trans'

-- rather than actually use cast and have to deal with it i'll just write my own
def castEq {n k} {n'} (h : n = n') (a : UpTo n k) : UpTo n' k where
  __ := a
  sum_parts := h ▸ a.sum_parts

attribute [simps] zero cons inclLe castEq


instance {k} : Unique (UpTo 0 k) where
  default := zero.inclLe (zero_le k)
  uniq a := by
    suffices a.parts = ∅ by ext : 1; simpa
    by_contra! ha
    rw [← nonempty_iff_ne_empty] at ha
    suffices 0 < ∑ p ∈ a.parts, p ^ 3 by simpa [a.sum_parts]
    apply sum_pos _ ha
    exact fun i hi => pow_pos (a.parts_bdd i hi).1 3

abbrev pushDown.ty n k :=
  match k with
  | 0 => PLift (n = 0)
  | k' + 1 => UpTo n k' ⊕ (k ^ 3 ≤ n) ×' UpTo (n - k ^ 3) k'

def pushDown {n k} (a : UpTo n k) : pushDown.ty n k :=
  match hk : k with
  | 0 => .up $ a.sum_parts ▸ sum_eq_zero fun p hp => by
    have := a.parts_bdd p hp; omega
  | k' + 1 =>
    if h : k ∈ a.parts then .inr
      { fst := a.sum_parts ▸ single_le_sum (fun i _ => zero_le (i ^ 3)) (hk.subst h)
        snd.parts := a.parts.erase k
        snd.parts_bdd := fun p hp => by
          rw [mem_erase] at hp
          have := a.parts_bdd p hp.2; omega
        snd.sum_parts := by
          apply Nat.eq_sub_of_add_eq
          simp_rw [← show k = k' + 1 from hk, sum_erase_add _ (· ^ 3) h, a.sum_parts] }
    else .inl
      { a with
        parts_bdd := fun p hp => by
          have hp' : p ≠ k := fun huh => absurd hp $ huh ▸ h
          have := a.parts_bdd p hp
          omega }

def pushDownEquiv n k : UpTo n k ≃ pushDown.ty n k where
  toFun := pushDown
  invFun a :=
    match k, a with
    | 0, ⟨h⟩ => zero.castEq h.symm
    | k' + 1, .inl a => a.inclLe k'.le_succ
    | k' + 1, .inr ⟨h, a⟩ => a.cons (k' + 1) k'.lt_succ_self |>.castEq (by omega)
  -- I don't really understand what's going on in these proofs at all,
  -- but hey, that's what the proof assistant is for!
  left_inv a := by
    unfold pushDown
    split
    . rename_i a
      obtain ⟨rfl⟩ := a.pushDown
      apply Subsingleton.elim
    rename_i k a _
    apply UpTo.ext
    split
    . rename_i h
      simpa using a.parts.insert_erase h
    . simp
  right_inv b := by
    match k with
    | 0 => rfl
    | k' + 1 =>
      have {n} (a : UpTo n k') : k' + 1 ∉ a.parts := fun hk => by
        have := a.parts_bdd _ hk; omega
      dsimp [pushDown]
      match b with
      | .inl a => simp [this a]
      | .inr ⟨h, a⟩ =>
        simp only [castEq_parts, cons_parts, cons_eq_insert, mem_insert, true_or, ↓reduceDIte,
          erase_insert_eq_erase]
        congr
        simp [this a]

-- building our fintype. this is so exciting!!
-- note that we've avoided using well-founded recursion, so the decide
-- tactic can reduce
instance instFintype n : ∀ k, Fintype (UpTo n k)
  | 0 => .ofEquiv _ (pushDownEquiv n 0).symm
  | k' + 1 =>
    let k := k' + 1
    letI := (instFintype · k')
    letI : Fintype ((k ^ 3 ≤ n) ×' UpTo (n - k ^ 3) k') :=
      if hk : k ^ 3 ≤ n then
        .ofEquiv (UpTo (n - k ^ 3) k')
          ⟨fun a => ⟨hk, a⟩, PProd.snd, fun _ => rfl, fun _ => rfl⟩
      else
        haveI : IsEmpty (k ^ 3 ≤ n) := isEmpty_Prop.mpr hk
        .ofIsEmpty
    .ofEquiv _ (pushDownEquiv n k).symm

end UpTo

def equivUpTo n k (h : n ≤ k ^ 3) : CubeyParty n ≃ UpTo n k where
  toFun a :=
    { parts := a.parts
      parts_bdd := fun p hp => by
        refine ⟨a.parts_pos _ hp, ?_⟩
        rw [← Nat.pow_le_pow_iff_left (show 3 ≠ 0 by norm_num)]
        exact h.trans' $ a.sum_parts ▸ single_le_sum (fun i _ => zero_le (i ^ 3)) hp
      sum_parts := a.sum_parts }
  invFun a :=
    { parts := a.parts
      parts_pos := fun p hp => a.parts_bdd _ hp |>.1
      sum_parts := a.sum_parts }
  left_inv a := rfl
  right_inv a := rfl



set_option maxRecDepth 42069 in
open scoped Cardinal in
theorem tada :
    (∀ n < 216, #(CubeyParty n) < 2) ∧ #(CubeyParty 216) = 2 := by
  have h n (hn : n ≤ 216) : #(CubeyParty n) = Fintype.card (UpTo n 6) := by
    rw [← Cardinal.mk_fintype]
    exact equivUpTo _ _ hn |>.cardinal_eq
  conv => arg 1; ext n; intro hn; rw [h n hn.le]
  rw [h 216 le_rfl]
  -- Not sure wtf norm_cast does if I run it by itself here,
  -- but it goes over the (base) max recursion depth??
  conv => arg 1; norm_cast
  conv => arg 2; norm_cast
  decide

end CubeyParty
