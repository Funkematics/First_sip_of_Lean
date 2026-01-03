open Classical


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
#check Nat → Nat → Nat
#check Nat.succ 2
#check Nat.add 3

--Create new types
def α : Type := Nat
def β : Type := Bool
#check Prod α β
#check α × β 

variable {p : Prop}
variable {q : Prop}

-- Should make nested functions explicit like thsi
theorem t1 : p → q → p :=
  fun hp : p =>
    fun hq : q =>
  show p from hp

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
    Iff.intro
      (fun h : p ∧ q => 
        show q ∧ p from And.intro (And.right h) (And.left h))
      (fun h : q ∧ p => 
        show p ∧ q from And.intro (And.right h) (And.left h))

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h
        (fun hp : p =>
          show q ∨ p from Or.intro_right q hp)
        (fun hq : q =>
          show q ∨ p from Or.intro_left p hq))
    (fun h : q ∨ p =>
      Or.elim h
        (fun hq : q =>
          show p ∨ q from Or.intro_right p hq)
        (fun hp : p => 
          show p ∨ q from Or.intro_left q hp))

--This one is not part of the problem set
example (C O : Prop)(h : C ∨ O) : O ∨ C := by
  exact Or.elim h
    (fun c => Or.inr c)
    (fun o => Or.inl o)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
    (fun h : (p ∧ q) ∧ r => 
      have hp : p ∧ q := And.left h
      have hpp : p := And.left hp
      have hpq : q := And.right hp
      have hr : r := And.right h
      show p ∧ (q ∧ r) from And.intro hpp (And.intro hpq hr))
    (fun h : p ∧ (q ∧ r) => 
      have hqr : q ∧ r := And.right h
      have hpq : q := And.left hqr
      have hpr : r := And.right hqr
      have hp : p := And.left h 
      show (p ∧ q) ∧ r from And.intro (And.intro hp hpq) hpr)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r => 
      Or.elim h                                       --split into 2 cases
        (fun hpq : (p ∨ q) => 
          Or.elim hpq                                 --further split into 2 cases
            (fun hp : p =>                            --case p
              show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hp )
            (fun hq : q =>                            --case q
              show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_left r hq ) ))
        (fun hr : r =>                                --case r
          show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_right q hr)))
    (fun h: p ∨ (q ∨ r) =>                            -- Backwards direction of proof
      Or.elim h 
        (fun hp : p =>                                --Need to remember order when using Or elimination
          show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_left q hp))
        (fun hqr : (q ∨ r) => 
          Or.elim hqr                                 -- We just split q v r, p hypothesis is separate sub-proof
            (fun hq : q => 
              show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_right p hq)) 
            (fun hr : r => 
              show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) hr )))
      

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := And.left h
      have hqr : (q ∨ r) := And.right h
      Or.elim hqr
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) (And.intro hp hq))
        (fun hr : r => 
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) (And.intro hp hr)))
    (fun h : (p ∧ q) ∨ (p ∧ r) => 
      Or.elim h
      (fun hpq : p ∧ q => 
         have hp : p := And.left hpq
         have hq : q := And.right hpq
         show p ∧ (q ∨ r) from And.intro hp (Or.intro_left r hq)) 
      (fun hpr : p ∧ r => 
        have hp : p := And.left hpr
        have hr : r := And.right hpr 
        show p ∧ (q ∨ r) from And.intro hp (Or.intro_right q hr)))



example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro                                       
    (fun h : p ∨ (q ∧ r) =>
      Or.elim h
        (fun hp : p => 
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.intro_left q hp) (Or.intro_left r hp))
        (fun hqr : q ∧ r =>
          have hq : q := And.left hqr
          have hr : r := And.right hqr
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.intro_right p hq) (Or.intro_right p hr)))
      (fun h : (p ∨ q) ∧ (p ∨ r) => 
        have hpq : p ∨ q := And.left h
        Or.elim hpq
          (fun hp : p =>
            show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp )
          (fun hq : q =>
            have hpr : p ∨ r := And.right h
            Or.elim hpr 
              (fun hp : p =>
                show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp)
              (fun hr : r =>
                show p ∨ (q ∧ r) from Or.intro_right p (And.intro hq hr))))


    -- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
    (fun h : (p → (q → r)) => 
      (fun hpq : p ∧ q => 
      have hp : p := And.left hpq
      have hq : q := And.right hpq
      show r from (h hp) hq))
    (fun h : (p ∧ q → r) => 
      (fun hp : p => 
        (fun hq : q => 
          show r from  h (And.intro hp hq))))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  Iff.intro
    (fun h : ((p ∨ q) → r) =>
      And.intro
        (fun hp : p => 
          show r from h (Or.intro_left q hp))
        (fun hq : q =>
          show r from h (Or.intro_right p hq)))
      (fun h : (p → r) ∧ (q → r) =>
        (fun hpq : p ∨ q => 
          Or.elim hpq
            (fun hp : p => 
              show r from (And.left h) hp)
            (fun hq : q =>
              show r from (And.right h) hq)))
  
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=       -- ¬(p ∨ q) is equal to (p ∨ q) → False, this is actually the same as the last proof
  Iff.intro
    (fun h : ¬(p ∨ q) =>
      And.intro
        (fun hp : p => 
          show False from h (Or.inl hp))  --using Or.inl notation to switch it up
        (fun hq : q =>
          show False from h (Or.inr hq)))
    (fun h : ¬p ∧ ¬q =>                     
      (fun hpq : p ∨ q => 
        Or.elim hpq
        (fun hp : p =>
          show False from (And.left h) hp )
        (fun hq : q =>
          show False from (And.right h) hq)))                   

example : ¬p ∨ ¬q → ¬(p ∧ q) :=                    -- (p → false) ∨ (q → false) → (p ∧ q) → false
    (fun h : ¬p ∨ ¬q =>
      fun hpq : (p ∧ q) =>                          -- ¬p ∨ ¬q → ¬(p ∧ q) by showing that p ∧ q → False
        Or.elim h                                   -- Producses two cases, ¬p is true and ¬q is true
          (fun hnp : ¬p =>                          -- Apply functions (negation is a function)
            show False from hnp (And.left hpq))
          (fun hnq : ¬q =>
            show False from hnq (And.right hpq)))
            
example : ¬(p ∧ ¬p) :=                               -- (p ∧ (p → false)) → false
 (fun h : (p ∧ ¬ p) => 
  have hp : p := And.left h
  have hnp : ¬p := And.right h
  show False from hnp hp)

example : p ∧ ¬q → ¬(p → q) :=                     -- p ∧ ¬q → (p → q) → false, so show (p → q) is false from intro
  (fun hpnq : p ∧ ¬q =>
    (fun ptq : (p → q) =>
    have hp : p := And.left hpnq
    have hnq : ¬q := And.right hpnq
    show False from hnq (ptq hp)))

example : ¬p → (p → q) := 
  (fun h : ¬p => 
    (fun hp : p => 
      have hf : False := h hp
      show q from False.elim hf))                 --This one is just confusing but mostly due to my 
                                                  --bad reading comprehension
                                                  --Turns out to be ex falso sequitur quodlibet or "principle of explosion"
example : (¬p ∨ q) → (p → q) := 
  (fun h : ¬p ∨ q => 
    (fun hp : p => 
      Or.elim h 
        (fun hnp : ¬p => 
          have hf : False := hnp hp               --A contradiction again
          show q from False.elim hf)
        (fun hq : q =>
          show q from hq)))

example : p ∨ False ↔ p :=                        --Trivial one
  Iff.intro
    (fun hpf : p ∨ False => 
      Or.elim hpf
        (fun hp : p => 
          show p from hp)
        (fun hf : False =>
          show p from False.elim hf))
    (fun hp : p => 
      show p ∨ False from Or.intro_left False hp)


example : p ∧ False ↔ False := 
  Iff.intro
    (fun hpf : p ∧ False => 
      have hp : p := And.left hpf
      have hf : False := And.right hpf
      show False from hf)
    (fun hf : False => 
      have hp : p := False.elim hf                --We can generate anything from False
      show p ∧ False from And.intro hp hf)

example : (p → q) → (¬q → ¬p) :=                  -- (p → q) → ((p → False) → (q → False)) This is contrapositive
  (fun ptq : p → q => 
    (fun nq : ¬q => 
      (fun hp : p => 
        show False from nq (ptq hp) )))


