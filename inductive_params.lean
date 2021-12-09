inductive List : Type -> Type 1
| nil  : Pi a : Type, List a
| cons : Pi a  :Type, a → List a → List a

#check @List.rec

open List

def list_rec(a : Type)(p : List a → Type)(pn : p (nil a))(pc : Π (x : a)(xs : List a), p xs → p (cons a x xs))(xs : List a): p xs :=
    @List.rec
        (λ b xs, Π
            (p : List b → Type)
            (pn : p (nil b))
            (pc : Π (x : b)(xs : List b), p xs → p (cons b x xs)),
                p xs)
        (λ a p pn pc, pn)
        (λ a x xs ih p pn pc, pc x xs (ih p pn pc))
        a xs p pn pc

#reduce list_rec

inductive Eq : Π a : Type, a → a → Type 1
| Refl : Π (a : Type)(x : a), Eq a x x

#check @Eq.rec

def Eq_rec(a : Type)(x : a)(p : Π (z : a), Eq a x z → Type)(px : p x (Eq.Refl a x))(y : a)(e : Eq a x y): p y e :=
    @Eq.rec
        (λ a x y e, Π
            (p : Π (z : a), Eq a x z → Type)
            (px : p x (Eq.Refl a x)),
                p y e)
        (λ a x p px, px)
        a x y e p px

#check @Eq_rec
