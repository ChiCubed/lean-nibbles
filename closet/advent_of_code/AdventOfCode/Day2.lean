import AdventOfCode.Utils.Parsec

namespace Day2

inductive Colour where | red | green | blue

structure Handful where (r g b : Nat)

structure Game where
  id : Nat
  reveals : Array Handful

section Parsing

open Lean (Parsec)
open Lean.Parsec

def colour : Parsec Colour :=
  pstring "red" *> pure .red <|>
  pstring "green" *> pure .green <|>
  pstring "blue" *> pure .blue

def handful : Parsec Handful := do
  let l ← many1SepStr ", " do
    let n ← nat
    skipString " "
    let c ← colour
    return (n, c)
  let mut res := Handful.mk 0 0 0
  for (n, c) in l do
    res := match c with
    | .red   => { res with r := res.r + n }
    | .green => { res with g := res.g + n }
    | .blue  => { res with b := res.b + n }
  return res

def game : Parsec Game := do
  skipString "Game "
  let id ← nat
  skipString ": "
  let reveals ← many1SepStr "; " handful
  return {id, reveals}

end Parsing

open Array

namespace Part1

def isPossible (g : Game) : Bool :=
  g.reveals.all fun h =>
    h.r ≤ 12 && h.g ≤ 13 && h.b ≤ 14

open Lean.Parsec in
def solveFile (path : System.FilePath) := do
  let mut sum := 0
  for l in ← IO.FS.lines path do
    let g ← IO.ofExcept <| (game <* eof).run l
    if isPossible g then
      sum := sum + g.id
  IO.println sum

#eval solveFile "inputs/2_input.txt"

end Part1


namespace Part2

-- surely this is "obviously" correct lol
def minimumSet (g : Game) : Handful := Id.run do
  let mut res := Handful.mk 0 0 0
  for h in g.reveals do
    res := {
      r := max res.r h.r
      g := max res.g h.g
      b := max res.b h.b
    }
  return res

open Lean.Parsec in
def solveFile (path : System.FilePath) := do
  let mut sum := 0
  for l in ← IO.FS.lines path do
    let g ← IO.ofExcept <| (game <* eof).run l
    let res := minimumSet g
    sum := sum + res.r * res.g * res.b
  IO.println sum

#eval solveFile "inputs/2_input.txt"

end Part2

end Day2
