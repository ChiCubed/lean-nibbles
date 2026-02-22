module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Basic

-- TODO: move this to a "ForMathlib" submodule or something
public import Mathlib.Algebra.Order.Ring.Cast

namespace Int
variable {R : Type*} [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]

@[expose] public def castOrderHom : ℤ →o R := ⟨Int.cast, cast_mono⟩
@[simp] public theorem coe_castOrderHom :
    ⇑(castOrderHom (R := R)) = (↑) :=
  rfl

end Int

namespace AMM.Q12582.Spec

@[expose] public section

open scoped Classical Finset in
/--
**12582.** *Proposed by Haoran Chen, Suzhou, China, Ilya Bogdanov, Moscow, Russia, and Fedor Petrov, St. Petersburg, Russia.*
A train with a fixed number of passenger cars runs along a line with several
stations. All passengers have advance reservations specifying the station where
they board the train and the station where they leave the train. Prove that,
for all possible passenger itineraries, the railroad can assign each passenger
to a car so that whenever the train is moving, the number of passengers in any
two cars differ by at most 1.

*NOTE: The line does need to be linear. The stations are represented by ℤ, and the overall route by ℝ.*
-/
def Solution : Prop :=
  ∀ (Car : Type*) [Fintype Car] [Nonempty Car],
  ∀ (Passenger : Type*) [Fintype Passenger],
  ∀ span : Passenger → NonemptyInterval ℤ,
  ∃ f : Passenger → Car,
  ∀ t : ℝ, t ∉ Set.range Int.cast →
  let s : Finset Passenger := {p | t ∈ (span p).map Int.castOrderHom}
  ∀ c₁ c₂ : Car,
    Nat.dist #{p ∈ s | f p = c₁} #{p ∈ s | f p = c₂} ≤ 1
