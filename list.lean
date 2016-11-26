/-
namespace hide
  constant list : Type → Type
  
  namespace list
    constant cons : Π A : Type, A → List A → list A
    constant nil : Π A : Type, list A
    constant head : Π A : Type, list A → A
    constant tail : Π A : Type, list A → list A
    constant append : Π A : Type, list A → list A → list A
  end list
end hide
-/
import data.list
open list 

check list

check @cons
check @nil
check @head
check @tail
check @append

import data.nat
open nat

constant vec : Type → nat → Type

namespace vec
  constant empty : Π A : Type, vec A 0
  constant cons : Π (A : Type) (n : nat), A → vec A n → vec A (n + 1)
  constant append : Π (A : Type) (n m: nat), vec A m → vec A n → vec A (n + m)
end vec

check vec.empty
check vec.cons
check vec.append

import data.sigma
open sigma

variable A : Type
variable B : A → Type
variable a : A
variable b : B a

check sigma.mk a b
check ⟨a, b⟩
check pr₁ ⟨a, b⟩
check pr₂ ⟨a, b⟩

eval pr₁ ⟨a, b⟩
eval pr₂ ⟨a, b⟩

open sigma.ops
open prod.ops

variables C D : Type
variables (c : C) (d : D)

eval (a, b).1
eval (a, b).2
eval ⟨c, d⟩.1
eval ⟨c, d⟩.2
