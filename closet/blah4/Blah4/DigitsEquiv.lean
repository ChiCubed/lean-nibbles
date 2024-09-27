import Mathlib.Data.Nat.Digits
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.List.toFinsupp

-- for Utils
namespace List

theorem enumFrom_take : ∀ (l : List α) i, enumFrom n (take i l) = take i (enumFrom n l)
| [], i | _, 0 | a::l, i+1 => by simp [enumFrom_take]

theorem enum_take : enum (take i l) = take i (enum l) := by simp [enum, enumFrom_take]

theorem mapIdx_take : mapIdx f (take i l) = take i (mapIdx f l) := by simp [mapIdx_eq_enum_map, map_take, enum_take]

-- theorem List.get_mapIdx

theorem sum_toFinsupp [Zero α] [AddCommMonoid M]
  (l : List α) [DecidablePred (getD l · 0 ≠ 0)]
  {f : ℕ → α → M} (hf : ∀ i, f i 0 = 0) :
l.toFinsupp.sum f = (l.mapIdx f).sum := by
  simp only [Finsupp.sum, toFinsupp, Finsupp.coe_mk]
  rw [Finset.sum_filter_of_ne fun x _ => mt fun h => h.substr <| hf x]
  conv_rhs => rw [← take_length l]
  generalize length l = n
  apply Finset.sum_range_induction
  . simp
  . intro n
    simp_rw [mapIdx_take, take_succ, sum_append]
    congr
    suffices : (get? l n |>.map (f n) |>.toList.sum) = f n (getD l n 0)
    . simpa [mapIdx_eq_enum_map]
    rw [getD_eq_get?, ← Option.getD_map (f n), hf]
    cases get? l n with | none => rfl | some _ => exact sum_singleton

end List

namespace Nat

variable {b : ℕ} [NeZero b]

def digitsFin (hb : 2 ≤ b) : ℕ → List (Fin b)
| 0 => []
| n+1 => ⟨(n+1) % b, mod_lt _ (NeZero.pos b)⟩ :: Nat.digitsFin hb ((n+1) / b)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) hb

theorem digitsFin_eq_digits (hb : 2 ≤ b) : ∀ n, ↑(digitsFin hb n) = digits b n
| 0 => by ext; simp [digitsFin]
| n+1 => by
  rw [digitsFin, digits_def' hb succ_pos']
  rw [Lean.Internal.coeM]
  simp
  simp [List.pure]


end Nat

namespace DigitsEquiv

open List

variable {b : ℕ} [NeZero b]
-- TODO i want 2 ≤ b to be like a "parameter" but is that just not a thing i can do :(



-- Why is the argument order for Finsupp.sum just bad }:<
def Nat.digitsEquiv (hb : 2 ≤ b) : ℕ ≃ (ℕ →₀ Fin b) :=
{ toFun := fun n => Nat.digitsFin hb n |>.toFinsupp
  invFun := fun d => d.sum <| fun i a => ↑a * b ^ i
  left_inv := by
    intro n
    simp

    rw [sum_toFinsupp]
    conv_rhs => rw [← Nat.ofDigits_digits b n, Nat.ofDigits_eq_sum_mapIdx]
    simp [mapIdx_eq_enum_map, enum_map, map_map]
    congr
    ext v
    simp
    rw [← mapIdx_eq_enum_map _ ]
    convert Nat.ofDigits_digits b n using 1
    

    simp
    set c := b.digits n |>.map (Fin.ofNat' · (NeZero.pos b))
    sorry
  right_inv := by
    sorry
  .. }

def Nat.digitsOrderIso : ℕ ≃o Lex (ℕᵒᵈ →₀ Fin b) :=
sorry

end DigitsEquiv