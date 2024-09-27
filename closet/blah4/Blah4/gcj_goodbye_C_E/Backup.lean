import Mathlib.Data.Nat.Interval
import Mathlib.Data.Finset.Sort

import Mathlib.Tactic.LibrarySearch

import Utils.List

import Blah4.gcj_goodbye_C_E.Spec


namespace gcj_goodbye_C_E


open List

variable {α : Type u} [LinearOrder α] [DecidableRel (· ≤ · : α → α → Prop)] (l : List α)

attribute [ext] ListPartition BadariWin AmirWin


-- Backup with all the ListPartition_equiv_splits nonsense.


section partition_equiv

theorem ListPartition.ext_length {l : List α} {p₁ p₂ : ListPartition l}
  (h : map length p₁.parts = map length p₂.parts) :
    p₁ = p₂ := by
  apply ListPartition.ext
  rw [eq_iff_join_eq]
  exact ⟨p₁.join_eq.trans <| .symm p₂.join_eq, h⟩

variable (l : List α)

def ListPartition_equiv_lengths :
    ListPartition l ≃ { a : List ℕ // (∀ x ∈ a, 0 < x) ∧ sum a = length l } :=
  { toFun := fun p =>
      ⟨map length p.parts,
       by simpa only [forall_mem_map_iff, length_pos] using p.parts_nonempty,
       by rw [← length_join, p.join_eq] ⟩
    invFun := fun ⟨a, a_pos, sum_eq⟩ =>
      ⟨l.splitInto a sum_eq,
       by simp only [← length_pos]
          rwa [← forall_mem_map_iff, splitInto_length],
       splitInto_join (h := sum_eq)⟩,
    left_inv := fun p => by
      apply ListPartition.ext_length
      simp [splitInto_length]
    right_inv := fun ⟨a, ha₁, ha₂⟩ => by simp [splitInto_length] }

def lengths_equiv_splits n :
    { a : List ℕ // (∀ x ∈ a, 0 < x) ∧ sum a = n } ≃
    { s // s ⊆ Finset.Icc 0 n ∧ 0 ∈ s ∧ n ∈ s } :=
  { toFun := fun ⟨a, a_pos, sum_eq⟩ =>
      let S := scanl (· + ·) 0 a
      have hS : S.Sorted (· < ·) := by
        rw [Sorted, ← chain'_iff_pairwise]
        apply Chain'_scanl
        simpa using a_pos
      have S_ne_nil : S ≠ [] := scanl_ne_nil
      have S_head : head S _ = 0 := head_scanl
      have S_getLast : getLast S S_ne_nil = n := by
        rw [getLast_scanl_eq_foldl, ← sum, sum_eq]
      ⟨⟨.ofList S, by exact hS.nodup⟩,
       fun x hx => by
         obtain ⟨⟨i, hi⟩, rfl⟩ := mem_iff_get.mp hx
         rw [Finset.mem_Icc, ← S_getLast, getLast_eq_get]
         refine ⟨zero_le', hS.get_strictMono.monotone ?_⟩
         simpa using Nat.le_pred_of_lt hi,
       by simpa using (show 0 ∈ S from S_head ▸ head_mem S_ne_nil),
       by simpa using (show n ∈ S from S_getLast ▸ getLast_mem S_ne_nil)⟩,
    invFun := fun ⟨s, hs, l_mem, r_mem⟩ =>
      let S := s.sort (· ≤ ·)
      let A := zipWith (· - ·) S.tail S
      have hS := s.sort_sorted_lt
      have s_ne : s.Nonempty := ⟨0, l_mem⟩
      have S_ne_nil : S ≠ [] := ne_nil_of_mem <| (Finset.mem_sort _).mpr l_mem
      have S_head : head S S_ne_nil = 0 := by
        have := get_zero (length_pos_of_ne_nil S_ne_nil)
        rw [head?_eq_head (h := S_ne_nil), Option.some_inj] at this
        rw [← this]; clear this
        change nthLe _ _ _ = 0
        rw [Finset.sorted_zero_eq_min']
        refine Nat.le_antisymm (Finset.min'_le _ _ l_mem) zero_le'
      have S_getLast : getLast S S_ne_nil = n := by
        rw [getLast_eq_nthLe, Finset.sorted_last_eq_max']
        refine Nat.le_antisymm ?_ (Finset.le_max' _ _ r_mem)
        rw [Finset.max'_le_iff]
        exact fun y hy => Finset.mem_Icc.mp (hs hy) |>.2
      ⟨A,
       fun x hx => by
         simp only [mem_iff_get, get_zipWith] at hx
         obtain ⟨n, rfl⟩ := hx
         suffices : get S ⟨n, _⟩ < get S ⟨n + 1, _⟩
         . simpa [get_tail]
         apply hS.get_strictMono
         simp,
       have : sum A = getLast S S_ne_nil - head S S_ne_nil :=
         let rec go : ∀ (l : List ℕ) (hl : l ≠ []) (hs : l.Sorted (· < ·)),
           sum (zipWith (· - ·) (tail l) l) = getLast l hl - head l hl
         | [] => by simp
         | [a] => by simp
         | a::b::l => fun hl hs => by
           suffices : b - a + sum _ = getLast _ _ - a
           . simpa
           have : sum (zipWith (· - ·) l (b::l)) = _ := go (b::l) (cons_ne_nil _ _) hs.tail
           rw [this, head_cons, add_comm]
           apply tsub_add_tsub_cancel
           . cases l with
             | nil => rfl
             | cons c l =>
               apply le_of_lt ∘ rel_of_sorted_cons hs.tail _
               rw [getLast]
               exact getLast_mem _
           . exact le_of_lt <| rel_of_sorted_cons hs _ <| .head _
         go S S_ne_nil hS
       by rw [S_head, S_getLast] at this; exact this⟩
    left_inv := fun ⟨a, a_pos, sum_eq⟩ =>
      let S := scanl (· + ·) 0 a
      -- TODO duplication help
      have hS : S.Sorted (· < ·) := by
        rw [Sorted, ← chain'_iff_pairwise]
        apply Chain'_scanl
        simpa using a_pos
      let rec go' : ∀ (l : List ℕ) (i : ℕ),
        let s := scanl (· + ·) i l
        zipWith (· - ·) (tail s) s = l
      | [], _ => rfl
      | [a], _ => by simp
      | a::b::l, i => by simpa using go' (b::l) (i + a)
      by
        simp only [Subtype.mk.injEq]
        set s : Finset ℕ := ⟨.ofList S, _⟩
        have : s.sort (· ≤ ·) = S := by
          rw [Finset.sort, Multiset.coe_sort]
          exact mergeSort_eq_self _ <| Pairwise.imp le_of_lt hS
        rw [this]
        apply go'
    right_inv := fun ⟨s, hs, l_mem, r_mem⟩ =>
      let S := s.sort (· ≤ ·)
      -- TODO more duplication :(
      have S_sorted : S.Sorted (· ≤ ·) := s.sort_sorted _
      have S_ne_nil : S ≠ [] := ne_nil_of_mem <| (Finset.mem_sort _).mpr l_mem
      have S_head : head S S_ne_nil = 0 := by
        have := get_zero (length_pos_of_ne_nil S_ne_nil)
        rw [head?_eq_head (h := S_ne_nil), Option.some_inj] at this
        rw [← this]; clear this
        change nthLe _ _ _ = 0
        rw [Finset.sorted_zero_eq_min']
        refine Nat.le_antisymm (Finset.min'_le _ _ l_mem) zero_le'
      let rec go'' : ∀ (l : List ℕ) (hl : l ≠ []) (hs : l.Chain' (· ≤ ·)),
        scanl (· + ·) (head l hl) (zipWith (· - ·) (tail l) l) = l
      | [] => by simp
      | [a] => by simp
      | a::b::l => fun hl hs => by
        cases hs with | cons hab ht =>
        simpa [hab] using go'' (b::l) (cons_ne_nil _ _) ht
      by
        simp only [Subtype.mk.injEq, ← Finset.val_inj]
        -- TODO clean this up jeez
        have := Multiset.sort_eq (· ≤ · : ℕ → ℕ → Prop) (scanl (· + ·) 0 <| zipWith (· - ·) (tail S) S)
        rw [← Finset.sort_eq (· ≤ ·) s, ← this, Multiset.coe_eq_coe, Multiset.coe_sort]
        rw [← S_head, go'' S S_ne_nil S_sorted.chain', mergeSort_eq_self _ S_sorted] }

def ListPartition_equiv_splits :=
  ListPartition_equiv_lengths l |>.trans <| lengths_equiv_splits _

#eval ListPartition_equiv_splits "sussy".toList |>.symm ⟨{0, 2, 3, 5}, by decide⟩


lemma ListPartition_equiv_lengths_length p : (ListPartition_equiv_lengths l p).val.length = p.parts.length := by
  simp [ListPartition_equiv_lengths]

lemma lengths_equiv_splits_card n a : (lengths_equiv_splits n a).val.card = a.val.length + 1 := by
  rcases a with ⟨a, _, _⟩
  simp [lengths_equiv_splits, length_scanl]

theorem ListPartition_equiv_splits_card p :
    (ListPartition_equiv_splits l p).val.card = p.parts.length + 1 := by
  rw [ListPartition_equiv_splits, Equiv.trans_apply,
    lengths_equiv_splits_card, ListPartition_equiv_lengths_length]

end partition_equiv



def solve_eq : Solution l (length l) :=
  let P := { p : ListPartition l // length p.parts = length l }
  let d : P := ⟨{ parts := map ([·]) l
                  parts_nonempty := by simp
                  join_eq := by induction l with
                  | nil => simp
                  | cons a l ih => simpa using ih },
                by simp ⟩
  letI : Unique P :=
    { default := d
      uniq := fun ⟨p, hp⟩ => by
        let φ := ListPartition_equiv_splits l
        have φ' := ListPartition_equiv_splits_card l
        rw [Subtype.mk.injEq, ← EmbeddingLike.apply_eq_iff_eq φ]
        suffices : ∀ {n s}, s ⊆ Finset.Icc 0 n → s.card = n + 1 → s = Finset.Icc 0 n
        . rw [Subtype.ext_iff]
          refine this (φ p).2.1 ?_ |>.trans <| symm <| this (φ d).2.1 ?_
          . simp_rw [← hp]; exact φ' p
          . simp_rw [← d.2]; exact φ' d
        intro n s hs card_eq
        refine Finset.eq_of_subset_of_card_le hs ?_
        rw [Nat.card_Icc]
        exact card_eq.ge }
  if h : l.Chain' (· ≤ ·) then .impossible ∘ .mk <|
    fun { p, num_parts, badari_loses } => badari_loses.false <|
      { parts := p.parts
        parts_perm := by simp
        sorted := by
          obtain rfl : p = _ := Subtype.ext_iff.mp <|
            show (⟨p, num_parts⟩ : P) = d from Subsingleton.allEq _ _
          rw [chain'_iff_pairwise] at h
          apply h.map
          intro a b; simp_rw [← not_lt]; exact mt <| fun | .rel h => h }
  else .possible
    { p.parts := map ([·]) l
      p.parts_nonempty := by simp
      p.join_eq := by clear h; induction l with
        | nil => simp
        | cons a l ih => simpa using ih
      num_parts := by simp
      badari_loses := .mk <| fun b => h <| by
        rcases b with ⟨parts, parts_perm, sorted⟩
        have H {a b} (_ : a ∈ parts) (hb : b ∈ map ([·]) l) : a ~ b ↔ a = b := by
          rw [mem_map] at hb
          rcases hb with ⟨b, _, rfl⟩
          apply perm_singleton
        rw [Forall₂.iff_of_mem H, forall₂_eq_eq_eq] at parts_perm
        rw [parts_perm] at sorted
        refine sorted.of_map (R := (· ≤ ·)) ([·]) ?_ |>.chain'
        intro a b; simp_rw [← not_lt]; exact mt .rel }


def solve_zero (hl : 0 < length l) : Solution l 0 :=
  .impossible ∘ .mk <| fun { p, num_parts, .. } => by
    rw [length_eq_zero] at num_parts
    exact length_pos.mp hl (num_parts ▸ p.join_eq).symm


def solve_one (hl : 1 < length l) : Solution l 1 :=
  .impossible ∘ .mk <| fun { p, num_parts, badari_loses } => badari_loses.false <|
    { parts := [l]
      parts_perm := by
        rcases p with ⟨parts, _, join_eq⟩
        rw [length_eq_one] at num_parts
        rcases num_parts with ⟨a, rfl⟩
        suffices : a = l
        . simpa using .of_eq this.symm
        simpa using join_eq
      sorted := sorted_singleton _ }


def solve_two (hl : 2 < length l) : Solution l 2 :=
  .impossible sorry


def solve_three (hl : 3 < length l) : Solution l 3 :=
  .impossible sorry


-- So we want a theorem like AmirWin_of_incommensurable
-- which states that if you find adjacent blocks in l,
-- say you have a decomposition l = s ++ a ++ b ++ t,
-- and reversed sort a > sort b.
-- then you can further partition s, t and you
-- get an AmirWin.

def solve_large (n : ℕ) (hl : n + 4 < length l) : Solution l (n + 4) :=
  if h : ¬ l.Chain' (· ≤ ·) then
    let rec go : (l : List α) → ¬ l.Chain' (· ≤ ·) →
        (a b : α) × (t : List α) ×' a::b::t ∈ tails l ∧ b < a
      | [] | [_] => fun h => by simp at h
      | a::b::l => fun h =>
        if hab : b < a then ⟨a, b, l, by simpa⟩
        else
          have ht := by
            rw [chain'_cons, not_and] at h
            exact h <| le_of_not_lt hab
          let ⟨a, b, t, ht, hab⟩ := go (b::l) ht
          ⟨a, b, t, .tail _ ht, hab⟩
    let ⟨a, b, t, ht, hab⟩ := go l h
    by
      simp?
      sorry
  else
    .impossible sorry


def solution n : Solution l n :=
  match h : compare l.length n with
  | .lt => .impossible ∘ .mk <| fun { p, num_parts, .. } =>
    let s := ListPartition_equiv_splits l p
    have s_card : s.val.card = n + 1 := num_parts ▸ ListPartition_equiv_splits_card l p
    have : n + 1 ≤ length l + 1 - 0 := s_card ▸ Nat.card_Icc _ _ ▸
      Finset.card_le_of_subset s.2.1
    Nat.le_of_succ_le_succ this |>.not_lt <| compare_lt_iff_lt.mp h
  | .eq => compare_eq_iff_eq.mp h ▸ solve_eq l
  | .gt =>
    let hl := compare_gt_iff_gt.mp h
    match hn : n with
    | 0 => solve_zero l (hn ▸ hl)
    | 1 => solve_one l (hn ▸ hl)
    | 2 => solve_two l (hn ▸ hl)
    | 3 => solve_three l (hn ▸ hl)
    | n+4 => solve_large l n (hn.subst hl)

-- TODO LinearOrder on Char
#eval solution ([] : List ℕ) 0

end gcj_goodbye_C_E