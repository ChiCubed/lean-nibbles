import Lean.Data.Parsec

namespace Lean.Parsec

open ParseResult

def many1Sep (sep : Parsec PUnit) (p : Parsec α) : Parsec (Array α) := do
  manyCore (sep *> p) #[←p]

def many1SepStr (sep : String) (p : Parsec α) : Parsec (Array α) :=
  many1Sep (skipString sep) p

-- would be nice to not have the "threat" of panicking but whatevs
def nat : Parsec Nat := do
  let s ← many1 digit
  return String.mk s.toList |>.toNat!

def asciiLetters : Parsec String :=
  many1Chars asciiLetter

-- read a newline
def nl : Parsec Unit := (skipChar '\r' <|> pure ()) *> skipChar '\n'

end Lean.Parsec
