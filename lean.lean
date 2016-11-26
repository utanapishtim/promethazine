import standard
open bool nat

constant m : nat
constant n : nat
constants b1 b2 : bool

check m
check n
check n + 0
check m * (n + 0)
check b1
check b1 && b2
check b1 || b2
check tt

open prod

constants m n : nat

constant f : nat →  nat
constant f' : nat →  nat
constant f'' : ℕ  →  ℕ
constant p : ℕ  × ℕ 
constant q : prod nat nat
constant g : nat →  nat →  nat
constant g' : nat →  (nat →  nat)
constant h : nat × nat →  nat

constant F : (nat →  nat) →  nat

check f
check f n
check g m n
check g m
check pair m n
check pr1 p
check pr2 p
check pr1 (pair m n)
check pair (pr1 p) n
check F f

check nat
check bool
check nat →  bool
check nat × bool
check nat →  nat
check nat × nat →  nat
check nat →  nat →  nat
check nat →  (nat →  nat)
check nat →  nat →  bool
check (nat →  nat) →  nat

constants A B : Type
constant F : Type →  Type
constant G : Type →  Type →  Type

check A
check F A
check F nat
check G A
check G A B
check G A nat

constants A B : Type

check prod
check prod A
check prod A B
check prod nat nat

import data.list
open list

constant A : Type

check list
check list A
check list nat

constants A B : Type
check A
check B
check Type
check Type →  Type

set_option pp.universes true

check A
check B
check Type
check Type →  Type

universe u
constant C : Type.{u}
check C
check A →  C

universe variable v
constants D E : Type
check D →  E
check D.{v} →  E.{v}

import data.nat data.bool
open nat bool

check fun x : nat, x + 5
check λ x : nat, x + 5

constants D E : Type
constants d1 d2 : D
constants e1 e2 : E

constant f : A →  A
constant g : A →  B
constant h : A →  B →  A
constant p : A →  A →  bool

check fun x : A, f x
check λ x : A, f x
