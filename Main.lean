import FirstSipOfLean
open Classical

def main : IO Unit := do
  IO.println "Test"

theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp

--Declaring objects and checking types
def m : Nat := 1
#check m
def b1 : Bool := true
#check b1
def b2 : Bool := false
#check b2
