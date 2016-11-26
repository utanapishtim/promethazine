/-
-- type parameter left explicit
namespace hide
constant list : Type → Type

namespace list
  constant cons : Π A : Type, A → list A → list A
  constant nil : Π A : Type, list A
  constant append : Π A : Type, list A → list A → list A
end list
end hide

open hide
open hide.list

variable A : Type
variable a : A
variables l1 l2 : list A

check cons A a (nil A)
check append A (cons A a (nil A)) l1
check append A (append A (cons A a (nil A)) l1) l2

check cons _ a (nil _)
check append _ (cons _ a (nil _)) l1
check append _ (append _ (cons _ a (nil _)) l1) l2
-/


-- implicit type parameter
namespace hide
constant list : Type → Type
/-
  the following type declarations inform lean that the type argument in the 
  definitions should be left implicit
-/
namespace list
  constant cons : Π {A : Type}, A → list A → list A
  constant nil : Π {A : Type}, list A
  constant append : Π {A : Type}, list A → list A → list A
end list
end hide

open hide
open hide.list

variable B : Type
variable b : B
variables l3 l4 : list B

check cons b nil
check append (cons b nil) l3
check append (append (cons b nil) l3) l4

definition ident {A : Type} (x : A) := x

set_option pp.metavar_args false --suppress metavariable arguments in type def

check ident


variables A B : Type
variables (a : A) (b: B)

check ident
check ident a
check ident b

-- variable declared with implict type param
variable {Z : Type}
variable z : Z
definition identi := z

variables X Y : Type
variables (x : X) (y : Y)

check identi
check identi x
check identi y

variable (n : nat)
check identi n

-- @<function> returns function will all implicit arguments explicit
check @identi
--check @identi x --won't type check
check @identi X
check @identi X x
check @identi Y
check @identi Y y
check @identi ℕ 
check @identi ℕ n
