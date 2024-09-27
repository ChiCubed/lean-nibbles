import Mathlib.Data.List.Perm
import Mathlib.Data.List.Sort
import Mathlib.Data.List.BigOperators.Basic

namespace List

section Sorted

variable {l₁ l₂ : List α} {R : α → α → Prop}

theorem Sorted.sublist (h₁ : l₁ <+ l₂) (h₂ : Sorted R l₂) : Sorted R l₁ :=
  Pairwise.sublist h₁ h₂

end Sorted

-- TODO in the stdlib,
-- get_zero_scanl and nthLe_zero_scanl have unnecessary assumptions
-- (is there some reason for it?)

section scanl

variable {f : β → α → β} {b : β} {l : List α}

@[simp]
theorem scanl_ne_nil : scanl f b l ≠ [] := ne_nil_of_length_pos <| length_scanl _ _ ▸ Nat.succ_pos _

@[simp]
theorem head?_scanl : head? (scanl f b l) = some b := by
  simp [← get?_zero]

@[simp]
theorem head_scanl : head (scanl f b l) scanl_ne_nil = b := by
  rw [← Option.some_inj, ← head?_eq_head, head?_scanl]

-- TODO is the use of ⦃⦄ here sussy
@[simp]
theorem get_scanl_eq_foldl_take :
    ∀ {b l i} ⦃h⦄, get (scanl f b l) ⟨i, h⟩ = foldl f b (take i l)
  | _, [], _ => by simp
  | _, a::l, 0 => fun h => rfl
  | _, a::l, i+1 => fun h => by
    rw [scanl, length_cons, Nat.succ_lt_succ_iff] at h
    exact get_scanl_eq_foldl_take (h := h)

@[simp]
theorem getLast_scanl_eq_foldl :
    getLast (scanl f b l) scanl_ne_nil = foldl f b l := by
  simp [getLast_eq_get, length_scanl]

end scanl

section Forall₂

theorem Forall₂.imp_of_mem : ∀ {l₁ : List α} {l₂ : List β},
    (∀ {a b}, a ∈ l₁ → b ∈ l₂ → R a b → S a b) → Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | [], [] | _::_, [] | [], _::_ => by simp
  | a::l₁, b::l₂ => fun h => by
    simp_rw [forall₂_cons]
    intro ⟨hab, ht⟩
    exact ⟨h (.head l₁) (.head l₂) hab,
           Forall₂.imp_of_mem (fun hc hd => h (.tail a hc) (.tail b hd)) ht⟩

theorem Forall₂.iff_of_mem (H : ∀ {a b}, a ∈ l₁ → b ∈ l₂ → (R a b ↔ S a b)) :
    Forall₂ R l₁ l₂ ↔ Forall₂ S l₁ l₂ :=
  ⟨Forall₂.imp_of_mem <| fun ha hb => H ha hb |>.mp,
   Forall₂.imp_of_mem <| fun ha hb => H ha hb |>.mpr⟩

end Forall₂


theorem Chain'_scanl : ∀ {l}, (∀ b, ∀ a ∈ l, R b (f b a)) → Chain' R (scanl f b l)
  | [] => by simp
  | a :: l => fun h => by
    apply Chain'.cons'
    . exact Chain'_scanl <| fun b a ha => h b a <| mem_cons_of_mem _ ha
    . simpa using h b a <| mem_cons_self _ _


theorem cons_head_tail {l : List α} (h : l ≠ []) : head l h :: tail l = l :=
  cons_head?_tail <| head?_eq_head _ _

-- getLast_mem already exists (????)
theorem head_mem : ∀ {l : List α} (h : l ≠ []), head l h ∈ l
  | [] => by simp
  | a::l => fun _ => .head l


theorem get_tail (l : List α) (i) :
    get l.tail i = get l ⟨i.1 + 1, lt_tsub_iff_right.mp <| length_tail l ▸ i.2⟩ := by
  cases l with
  | nil => exact (length_nil ▸ i).elim0
  | cons a l => simp

section sublist

variable {l₁ l₂ : List α} (hs : l₁ <+ l₂)

theorem tail_sublist_of_sublist :
    ∀ {l₁ l₂ : List α} (_ : l₁ <+ l₂), tail l₁ <+ tail l₂
  | _, _, .slnil => .slnil
  | _, _, .cons _ h => tail_sublist_of_sublist h |>.trans <| tail_sublist _
  | _, _, .cons₂ _ h => h

theorem dropLast_sublist_of_sublist :
    ∀ {l₁ l₂ : List α} (_ : l₁ <+ l₂), dropLast l₁ <+ dropLast l₂
  | _, _, .slnil => .slnil
  | [_], _, _ => nil_sublist _
  | [], [_], .cons _ _ => .slnil
  | _, _::_::_, .cons _ h => .cons _ <| dropLast_sublist_of_sublist h
  | _::_::_, _::_::_, .cons₂ _ h => .cons₂ _ <| dropLast_sublist_of_sublist h

end sublist


section splitInto

def splitInto : ∀ (l : List α) (a : List ℕ) (_ : sum a = length l), List (List α)
  | _, [] => fun _ => []
  | l, x::a => fun h => let s := l.splitAt x; cons s.1 <| splitInto s.2 a <| by
    have := symm <| Nat.sub_eq_of_eq_add <| Nat.add_comm _ _ ▸ h.symm.trans sum_cons
    simpa

theorem splitInto_length : ∀ {l : List α} {a} ⦃h⦄, (splitInto l a h).map length = a
  | _, [] => fun _ => rfl
  | _, _::_ => fun h => by
    rw [sum_cons] at h
    simp [le_self_add.trans_eq h, splitInto_length]

theorem splitInto_join : ∀ {l : List α} {a} ⦃h⦄, (splitInto l a h).join = l
  | _, [] => fun h => by symm at h ⊢; simpa [← length_eq_zero]
  | _, _::_ => fun h => by simp [splitInto_join]

end splitInto


end List