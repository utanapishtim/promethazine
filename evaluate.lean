import data.nat data.prod data.bool
open nat prod bool

constants m n : nat
constant b : bool

print "reducing pairs"
eval pr1 (pair m n) -- m
eval pr2 (pair m n) -- n

print "reducing boolean expressions"
eval tt && ff -- ff
eval b && ff  -- ff

print "reducing arithmetic expressions"
eval n + 0         -- n
eval n + 2         -- succ (succ n)
eval (2 : nat) + 3 -- 5


constants A B C : Type
constants (a : A) (f : A → B) (g : B → C) (h : A → A)

definition gfa : C := g (f a)

check gfa
print gfa

definition gfa' := g (f a)
check gfa'
print gfa'


definition gfha := g (f (h a))
check gfha
print gfha

definition g_comp_f : A → C : λ x, g (f x)
check g_comp_f
print g_comp_f
