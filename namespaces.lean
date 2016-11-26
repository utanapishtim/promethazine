namespace foo
  constant A : Type
  constant a : A
  constant f : A → A

  definition fa : A := f a

  namespace bar
    definition ffa : A := f (f a)

    check fa
    check ffa
  end bar

  check fa
  check bar.ffa
end foo

check foo.fa
check foo.bar.ffa

open foo

check fa
check bar.ffa
