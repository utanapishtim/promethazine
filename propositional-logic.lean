variables p q : Prop

check p → q → p ∧ q
check ¬p → q ↔ false
check p ∨ q → q ∨ p

/-
  order of operations:
  1. ¬ 
  2. ∧, ∨ 
  3. → , ↔ 

  → is right associative
-/

-- CONJUNCTION:

-- create a proof of p →  q →  p ∧ q

-- 'example' state a theorem without naming it or storing it in the permanent
-- context
example (Hp : p) (Hq : q) : p ∧ q := and.intro Hp Hq

check assume (Hp : p) (Hq : q), and.intro Hp Hq

-- and.elim_left H and and.elim_right H create a proof of p and q
-- respectively from a proof H : p ∧ q

example (H : p ∧ q) : p := and.elim_left H
example (H : p ∧ q) : q := and.elim_right H

-- a proof of p ∧ q → q ∧ p 
-- using convenience methods 'and.right' and 'and.left'
example (H: p ∧ q) : q ∧ p :=
and.intro (and.right H) (and.left H)

/-
  it is interesting to note that and-intro and and-elim are similar in
  structure to the pairing and projection operations for the cartesian
  product.

  The difference lies in the type:
  
  and.intro Hp Hq has type p ∧ q : Prop
  
  pair Hp Hq has type p × q : Type

  another result of curry-howard, though lean treats them separately

-/

-- DISJUNCTION:

-- disjunction introduction
example (Hp : p) : p ∨ q := or.intro_left q Hp
example (Hq : q) : p ∨ q := or.intro_right p Hq

/-
  disjunction elimination is interesting. 

  to prove r from p ∨ q we must prove BOTH p → r and q → r

  'or.elim' takes three args
    1. p ∨ q
    2. p → r
    3. q → r
  and returns a proof of r
-/

-- a proof of p ∨ q → q ∨ p
example (H : p ∨ q) : q ∨ p :=
or.elim H
  (assume Hp : p,
    show q ∨ p, from or.intro_right q Hp)
  (assume Hq : q,
    show q ∨ p, from or.intro_left p Hq)
/-
  or.inr and or.inl abbreviate or.intro_right and or.intro_left, respectively  , also inferring the first type of their unabbreviated counterparts.
-/ 

example (H : p ∨ q) : q ∨ p := or.elim H (λ Hp, or.inr Hp) (λ Hq, or.inl Hq)

-- NEGATION AND FALSITY
/-
  not.intro H produces a proof of ¬p from H : p → false, that is, if we can
  derive a contradiction from p.

  not.elim Hnp Hp produces a proof of false from Hp : p and Hnp : ¬p
-/

-- a proof of (p → q) → ¬q → ¬p
example (Hpq: p → q) (Hnq : ¬q) : ¬p :=
not.intro 
  (assume Hp : p, 
    show false, from not.elim Hnq (Hpq Hp))

/-
  not.intro is an abbreviation for p → false, so not.intro amounts to the
  introduction rule for implication. Similarly, not.elim is the function
  ¬p → p → false, i.e. simple function application.

  We can, therefore, avoid the use of not.intro and not.elim entirely in
  favor of abstraction and elimination, as seen below:
-/

example (Hpq : p → q) (Hnq : ¬q) : ¬p :=
assume Hp : p, Hnq (Hpq Hp)

/-
  false hasa single elimination rule, false.elim, which express the fact
  that anything follows from a contradiction. Called 'ex false', short for
  'ex falso sequitur quodlibet', or 'the principle of explosion'
-/

example (Hp : p) (Hnp : ¬p) : q := false.elim (Hnp Hp)

-- absurd is sugar for false.elim
example (Hp : p) (Hnp : ¬p) : q := absurd Hp Hnp

-- a proof of: ¬p → q → (q → p) → r
example (Hnp : ¬p) (Hq : q) (Hqp : q → p) :r :=
absurd (Hqp Hq) Hnp

-- true has one introduction rule, true.intro : true; abbrviated 
-- trivial : true

-- LOGICAL EQUIVALENCE
-- iff.intro H1 H2 -> p ↔ q from H1 : p → q and H2 : q → p
-- iff.elim_right H -> p → q from H : p ↔ q
-- iff.elim_left H -> q → p from H : p ↔ q

-- proof of p ∧ q ↔ q ∧ p
theorem and_swap : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume H : p ∧ q,
    show q ∧ p, from and.intro (and.right H) (and.left H))
  (assume H : q ∧ p,
    show p ∧ q, from and.intro (and.right H) (and.left H))

check and_swap p q

-- iff.elim_left and iff.elim_right can be abbreviated iff.mp and iff.mpr, 
-- respectively


section
  variables p q : Prop
  -- have introduces and 'auxiliary subgoal' in a proof
  example (H : p ∧ q) : q ∧ p :=
  have Hp : p, from and.left H,
  have Hq : q, from and.right H,
  show q ∧ p, from and.intro Hq Hp
end

-- 'have H : p, from s, t' produces '(λ (H : p), t) s'
-- in other words, s is a proof of p, t is a proof of the desired conclusion
-- assuming H : p

-- excluded middle
open classical
variable p : Prop
check em p

-- double negation
theorem dne {p : Prop} (H : ¬¬p) : p :=
or.elim (em p)
  (assume Hp : p, Hp)
  (assume Hnp : ¬p, absurd Hnp H)

-- assuming ¬p and deriving false, we have a proof for p; namely, 
-- a proof by contradiction
example (H : ¬¬p) : p :=
by_cases
  (assume H1 : p, H1)
  (assume : ¬p, absurd H1 H)

example (H : ¬¬p) : p :=
by_contradiction
  (assume H1 : ¬p,
    show false, from H H1)

-- de-morgans
example (H : ¬ (p ∧ q)) : ¬ p ∨ ¬ q :=
or.elim (em p)
  (assume Hp : p,             
    or.inr
      (show ¬q, from          
        assume Hq : q,
        H (and.intro Hp Hq)))
  (assume Hp : ¬p,
    or.inl Hp)
