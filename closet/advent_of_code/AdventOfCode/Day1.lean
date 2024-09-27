import Std.Data.String
import Std.Data.RBMap
open Std (RBMap)

namespace String

section

instance instOrdPos : Ord Pos where
  compare x y := compareOfLessAndEq x y

variable (s : String) (patterns : Array Substring)

-- it seems like lemmata for String.Matcher stuff
-- don't exist, so let's write our own substring finder I guess

def findAllSubstrInArray : Array Substring :=
  patterns.map s.findAllSubstr |> .flatten

def findFirstSubstrInArray? : Option Substring :=
  findAllSubstrInArray s patterns |>
  Array.min? (ord := Ord.on (Ord.lex instOrdPos instOrdPos)
    fun s => (s.startPos, s.stopPos))

def findLastSubstrInArray? : Option Substring :=
  findAllSubstrInArray s patterns |>
  Array.max? (ord := Ord.on (Ord.lex instOrdPos instOrdPos)
    fun s => (s.stopPos, s.startPos))

def findFirstSubstrInArray! :=
  findFirstSubstrInArray? s patterns |> Option.get!

def findLastSubstrInArray! :=
  findLastSubstrInArray? s patterns |> Option.get!

end

end String

namespace Std.RBMap

def findEntry (t : RBMap α β cmp) {k : α} (h : t.contains k) :=
  t.findEntry? k |>.get h

def find (t : RBMap α β cmp) (k : α) (h : t.contains k) :=
  t.findEntry h |>.snd

end Std.RBMap

namespace Day1

open Array

def numberMap : RBMap String Nat compare :=
  (List.range 10).map (fun n => (toString n, n)) |>.toRBMap _

def solve (s : String) : Nat :=
  let numberNames := numberMap.keysArray.map String.toSubstring
  let a := s.findFirstSubstrInArray! numberNames |>.toString
  let b := s.findLastSubstrInArray! numberNames |>.toString

  have ha : numberMap.contains a := by

    sorry
  have hb : numberMap.contains b := by
    sorry

  10 * (numberMap.find ha) + (numberMap.find hb)

def solveFile (path : System.FilePath) := do
  IO.println <| foldl (· + ·) 0 <| map solve <| ← IO.FS.lines path

#eval solveFile "inputs/1_sample.txt"

end Day1
