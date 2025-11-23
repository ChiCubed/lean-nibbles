import Mathlib.Tactic

section Givens
  -- Mathlib already has something called Tree
  inductive Tree' : Type where
  | leaf : Tree'
  | branch : Tree' → Tree' → Tree'

  def toList (d : Nat) : Tree' → List Nat
  | .leaf => [d]
  | .branch t₁ t₂ => toList d.succ t₁ ++ toList d.succ t₂
end Givens


/-
proof by left inverse
-/
namespace Proof1
  attribute [local simp] toList

  @[local simp, local grind .] theorem toList_ne_nil {d t} : toList d t ≠ [] := by
    fun_induction toList <;> simp_all

  @[local grind .] theorem head_toList_ge {d t} : d ≤ (toList d t).head toList_ne_nil := by
    fun_induction toList <;> (simp_all <;> omega)

  -- this def still makes me a bit saD :( i wan smoething
  -- which doesnt need proving length_ofList_lt or whatever
  def ofList (d : Nat) (as : List Nat) : Tree' × List Nat :=
    if h : as = [] then
      (.leaf, [])
    else
      let a := as.head h
      if d = a then
        (.leaf, as.tail)
      else if d < a then
        have : as.headI = a := by grind [List.headI.eq_def]
        let (u, bs) := ofList d.succ as
        -- the if always fires, this is just to convince Lean of termination
        let (v, cs) := if bs.length < as.length then ofList d.succ bs else (.leaf, [])
        (.branch u v, cs)
      else
        (.leaf, [])
  termination_by (as.length, as.headI - d)

  @[local grind .] theorem length_ofList_lt {d l} : (ofList d l).2.length ≤ l.length - 1 := by
    induction hl : l.length using Nat.strong_induction_on generalizing d l; grind [ofList]

  theorem ofList_toList {d l t} : ofList d (toList d t ++ l) = (t, l) := by
    induction t generalizing d l <;> grind [toList, ofList, List.length_pos_iff]

  theorem toList_injective {n t t'} : toList n t = toList n t' → t = t' := fun h => by
    convert congr(ofList n ($h ++ []) |>.1) <;> rw [ofList_toList]
end Proof1


/-
proof by quaint potential
-/
namespace Proof2
  attribute [local simp] toList

  theorem toList_invar {d t} : (toList d t |>.map ((2⁻¹ : ℚ) ^ ·)).sum = 2⁻¹ ^ d := by
    fun_induction toList <;> (simp_all <;> ring)

  theorem length_toList_eq_one_iff {d t} : (toList d t).length = 1 ↔ t = .leaf := by
    suffices 0 < (toList d t).length ∧ _ from this.2
    fun_induction toList <;> (simp_all <;> omega)

  theorem toList_injective {n t t'} : toList n t = toList n t' → t = t' := fun h => by
    match t, t' with
    | .leaf, .leaf => rfl
    | .leaf, .branch .. | .branch .., .leaf => grind [length_toList_eq_one_iff]
    | .branch t₁ t₂, .branch t₁' t₂' =>
      rw [toList, toList, List.append_eq_append_iff] at h
      rcases h with ⟨l, h₁, h₂⟩ | ⟨l, h₁, h₂⟩
      all_goals
        have : (l |>.map ((2⁻¹ : ℚ) ^ ·)).sum = 0 := by grind [toList_invar]
        apply List.all_zero_of_le_zero_le_of_sum_eq_zero (by simp) at this
        obtain rfl : l = [] := List.eq_nil_iff_forall_not_mem.mpr <| by simpa
        simp_all; solve_by_elim [toList_injective]
  termination_by sizeOf t + sizeOf t'
end Proof2


/-
proof by being smart
-/
namespace Proof3
  attribute [local simp, local grind] toList

  @[local simp, local grind .] theorem toList_ne_nil {d t} : toList d t ≠ [] := by
    fun_induction toList <;> simp_all

  @[local grind! .] theorem head_toList_ge {d t} : d ≤ (toList d t).head toList_ne_nil := by
    fun_induction toList <;> (simp_all <;> omega)

  theorem toList_injective.aux {n t t' l l'} (h : toList n t ++ l = toList n t' ++ l') :
      t = t' ∧ l = l' := by
    match t, t' with
    | .leaf, .leaf | .leaf, .branch .. | .branch .., .leaf => grind [! => List.head_append_left]
    | .branch .., .branch .. =>
      simp only [toList, List.append_assoc] at h
      have ⟨rfl, h⟩ := aux h
      have ⟨rfl, h⟩ := aux h
      exact ⟨rfl, h⟩

  theorem toList_injective {n t t'} : toList n t = toList n t' → t = t' := fun h =>
    toList_injective.aux congr($h ++ []) |>.1
end Proof3
