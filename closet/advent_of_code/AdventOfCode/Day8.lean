import AdventOfCode.Utils.Parsec
import Mathlib.Data.Finsupp.Basic
import Std.Data.HashMap.Basic

open Std

namespace Day8

section Spec

inductive Dir | L | R

structure Adj (a : Type _) where
  (node left right : a)
deriving DecidableEq

abbrev AdjArray a := Array (Adj a)

instance [Zero a] : Zero (b → a) :=
  ⟨fun _ => 0⟩

structure Graph [Zero a] (a : Type _) where
  move : a →₀ Dir → a

def Graph.ofEdges [Zero a] [BEq a] [Hashable a] (adjs : AdjArray a) :
    Graph a := Id.run do
  let mut h : HashMap a (a × a) := mkHashMap
  for { node, left, right } in adjs do
    h := h.insert node (left, right)
  return ⟨fun n =>
    let nexts := h.findD n (n, n)
    fun | .L => nexts.1 | .R => nexts.2⟩

end Spec

section Parsing

open Lean (Parsec)
open Lean.Parsec

def dir : Parsec Dir :=
  pstring "L" *> pure .L <|>
  pstring "R" *> pure .R

def adj : Parsec (Adj String) := do
  let node ← asciiLetters
  skipString " = ("
  let left ← asciiLetters
  skipString ", "
  let right ← asciiLetters
  skipString ")"
  return { node, left, right }

def everything : Parsec (Array Dir × Graph String) := do
  let dirs ← many1 dir
  nl; nl
  let adjs ← many1Sep nl adj
  nl <|> pure ()
  eof
  return (dirs, .ofEdges adjs)

end Parsing

namespace Part1

def calcWinTime [BEq a] [Hashable a] (G : Graph a)
  (dirs : Array Dir) (s t : a) :
    Option Nat := do
  let mut c := s
  let mut i := 0
  for wah in range G.move.support.card do
    for d in dirs do
      c := G.move c d
      if c = t then
        return i
      i := i + 1
  return .none

theorem calcWinTime_spec : sorry := sorry

def solveFile (path : System.FilePath) := do
  let s ← IO.FS.readFile path
  let ⟨dirs, G⟩ ← IO.ofExcept <| everything.run s
  IO.println <| calcWinTime G dirs "AAA" "ZZZ"

#eval solveFile "inputs/8_sample1.txt"
#eval solveFile "inputs/8_sample2.txt"

end Part1

end Day8
