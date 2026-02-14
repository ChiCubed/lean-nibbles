import Mathlib

/-
a verified imperative sieve of eratosthenes using `mvcgen` and `grind`! :O
-/

macro_rules
  | `([ $start : $stop : $step ]) => `({ start := $start, stop := $stop, step := $step, step_pos := by grind : Std.Legacy.Range })
  | `([ : $stop : $step ]) => `({ stop := $stop, step := $step, step_pos := by grind : Std.Legacy.Range })

attribute [grind →] Membership.mem.lower Membership.mem.upper Membership.mem.step

def primesLt (n : Nat) : Id (Array Nat) := do
  let mut prime? := Vector.replicate n true
  prime? := prime?.setIfInBounds 0 false
  prime? := prime?.setIfInBounds 1 false
  let mut primes := #[]
  for hp : p in [2:n] do
    if prime?[p] then
      primes := primes.push p
      for hm : m in [p*p:n:p] do
        prime? := prime?.set m false
  return primes


section BoringLemmas
  theorem List.mem_range'_pos {s step m n} (h : 0 < step) :
      m ∈ range' s n step ↔ s ≤ m ∧ m < s + step * n ∧ step ∣ m - s := by
    rw [mem_range']
    refine ⟨by aesop, ?_⟩
    rintro ⟨hl, hu, hd⟩
    apply Nat.exists_eq_add_of_le at hl
    obtain ⟨m, rfl⟩ := hl
    rw [add_tsub_cancel_left] at hd
    apply exists_eq_mul_right_of_dvd at hd
    obtain ⟨m, rfl⟩ := hd
    exists m
    simpa [h] using hu

  theorem Std.Legacy.Range.mem_iff_dvd (x : Nat) (r : Range) :
      x ∈ r ↔ r.start ≤ x ∧ x < r.stop ∧ r.step ∣ x - r.start := by
    simp [instMembershipNatRange, ← Nat.dvd_iff_mod_eq_zero]

  @[simp, grind _=_] theorem Std.Legacy.Range.mem_toList_iff (x : Nat) (r : Range) :
      x ∈ r.toList ↔ x ∈ r := by
    refine ⟨mem_of_mem_range', ?_⟩
    rw [List.mem_range'_pos r.step_pos, mem_iff_dvd, ← Nat.ceilDiv_eq_add_pred_div]
    suffices r.start ≤ x → r.step ∣ x - r.start →
        (x < r.stop ↔ x < r.start + r.step * ((r.stop - r.start) ⌈/⌉ r.step)) by tauto
    intro hl hd
    apply Nat.exists_eq_add_of_le at hl
    obtain ⟨x, rfl⟩ := hl
    rw [add_tsub_cancel_left] at hd
    apply exists_eq_mul_right_of_dvd at hd
    obtain ⟨x, rfl⟩ := hd
    rw [← Nat.lt_sub_iff_add_lt', ← Nat.lt_sub_iff_add_lt', add_tsub_cancel_left,
      Nat.mul_lt_mul_left r.step_pos, lt_iff_not_ge (a := x), ceilDiv_le_iff_le_mul r.step_pos, ← lt_iff_not_ge]

  @[grind →] theorem List.pref_of_range'_eq_append_cons {s n step xs cur ys} (h : range' s n step = xs ++ cur :: ys) :
      xs = range' s xs.length step := by
    grind only [range'_eq_append_iff, = length_range']
end BoringLemmas


@[simp, grind =] lemma primesLt.spec.aux {i p n : ℕ} (hp : 0 < p) : i ∈ [p*p:n:p] ↔ p * p ≤ i ∧ i < n ∧ p ∣ i := by
  simp +contextual [Std.Legacy.instMembershipNatRange, ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_sub_iff_left]

open Std.Do in
attribute [local grind! .] Nat.minFac_prime Nat.prime_def_minFac Nat.minFac_dvd Nat.minFac_le in -- TOOD this stuff sdumb
attribute [local grind →] Nat.Prime.two_le in
set_option maxHeartbeats 10000000 in
@[spec] theorem primesLt.spec n :
    ⦃⌜True⌝⦄ primesLt n ⦃⇓r => ⌜(∀ p, p ∈ r ↔ p < n ∧ p.Prime) ∧ r.toList.SortedLE⌝⦄ := by
  mvcgen [primesLt]
  invariants
  | inv1 =>
    ⇓⟨pos, ⟨prime?, primes⟩⟩ =>
      ⌜(∀ i (hi : i < n), prime?[i] ↔
          i ∈ pos.prefix ∧ i.Prime ∨
          2 ≤ i ∧ i.minFac ∉ pos.prefix) ∧
       primes.toList = pos.prefix.filter (·.Prime)⌝
  | inv2 pref _ _ _ _ _ _ _ _ _ =>
    ⇓⟨pos, prime?⟩ =>
      ⌜∀ i (hi : i < n), prime?[i] ↔
         i ∈ pref ∧ i.Prime ∨
         2 ≤ i ∧ i.minFac ∉ pref ∧ i ∉ pos.prefix⌝
  with simp_all +zetaDelta
  case vc1.step p _ _ _ _ _ _ pm m _ _ _ _ _ _ _ =>
    -- lol why did the old proof stop working? how did it even work anyway?
    suffices ¬ m.Prime by simp [Vector.getElem_set]; grind
    have : m = p * (p + pm.length) := by grind
    rw [this]
    apply Nat.not_prime_mul <;> grind
  case vc3.step.isTrue.post.success =>
    -- TODO `=_ Nat.lt_mul_self_iff` is doing something silly but hey if it works it works
    grind (splits := 15) [Nat.minFac_sq_le_self, Nat.pow_two, → Nat.minFac_le_of_dvd, =_ Nat.lt_mul_self_iff]
  case vc4.step.isFalse => grind [=> List.mem_append_left]
  case vc5.pre => grind
  case vc6.post.success => grind [=_ Array.mem_toList_iff, List.sortedLT_range']
