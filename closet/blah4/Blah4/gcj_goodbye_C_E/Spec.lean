import Mathlib.Init.Algebra.Order
import Mathlib.Data.List.Perm
import Mathlib.Data.List.Sort
import Mathlib.Data.List.BigOperators.Basic


namespace gcj_goodbye_C_E

section Specification

open List

variable {α : Type u} [LinearOrder α] [DecidableRel (· ≤ · : α → α → Prop)] (l : List α)

structure ListPartition where
  parts : List (List α)

  -- TODO you could alternately write [] ∉ parts; is that better? worse?
  parts_nonempty : ∀ x ∈ parts, x ≠ []
  join_eq : parts.join = l
deriving Repr

structure BadariWin {l} (p : ListPartition l) where
  parts : List (List α)

  parts_perm : Forall₂ (· ~ ·) parts p.parts
  sorted : parts.Sorted (· ≤ ·)
deriving Repr

structure AmirWin (n : ℕ) where
  p : ListPartition l

  num_parts : p.parts.length = n
  badari_loses : IsEmpty (BadariWin p)
deriving Repr

inductive Solution (n : ℕ) where
| possible : AmirWin l n → Solution n
| impossible : IsEmpty (AmirWin l n) → Solution n

-- TODO: for some reason deriving Repr doesn't work
-- so here's a minimal little thingy
instance [Repr α] : Repr <| Solution l n where
  reprPrec := fun s _ => match s with
    | .possible a => ".possible " ++ repr a
    | .impossible _ => ".impossible _"

end Specification

end gcj_goodbye_C_E
