import data.nat
open nat

constants (m n : nat) (p q : bool)

definition m_plus_n : nat := m + n
check m_plus_n
print m_plus_n

-- lean can infer the type
definition m_plus_n' := m + n

definition double (x : nat) : nat := x + x
print double
check double 3
eval double 3

definition square (x : nat) := x * x
print square
check square 3
eval square 3

definition do_twice (f: nat → nat) (x : nat) : nat := f (f x)
eval do_twice double 2

definition do_twice' : (nat → nat) → nat → nat := λ f x, f (f x)
eval do_twice' double 2

import data.prod
open prod
definition curry (A B C : Type) (f : A × B → C) : A → B → C := λ x, (λ y, f (pair x y))

definition fn (x : nat × nat) : ℕ := (pr1 x) + (pr2 x)
check fn
check ℕ
check curry ℕ ℕ ℕ fn 1 2
eval curry ℕ ℕ ℕ fn 1 2

definition uncurry (A B C : Type) (f : A → B → C) : A × B → C := λ x, (f (pr1 x)) (pr2 x)

check uncurry

definition curriedFn := curry ℕ ℕ ℕ fn
check curriedFn

check uncurry ℕ ℕ ℕ curriedFn 
eval uncurry ℕ ℕ ℕ curriedFn (pair 1 2)

check let y := n + n in y * y
definition t (x : ℕ ) : ℕ := let y := x + x in y * y
eval t 3
eval t 2
eval t 1

definition h (n : ℕ ) : ℕ  := let y := n + n, z := y + y in z * z
eval h 1
eval h 2

definition foo := let a := nat in λ x : a, x + 2
eval foo 1

/-
definition bar := (λ a, λ x : a, x + 2) nat
-/

