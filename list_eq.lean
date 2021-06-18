inductive Eq (a : Type)(x : a): a → Type
| mk : Eq x

inductive Void : Type

open list

def list_eq(a : Type): list a → list a → Type
| nil nil := unit
| nil (cons _ _) := Void
| (cons _ _) nil := Void
| (cons x xs) (cons y ys) := (Eq a x y) × list_eq xs ys

def list_refl (a : Type): ∀ xs : list a, list_eq a xs xs
| nil := unit.star
| (cons x xs) := prod.mk (Eq.mk x) (list_refl xs)

def J: ∀ (a : Type)(xs : list a)(p : ∀ ys : list a, list_eq a xs ys → Type)(prefl : p xs (list_refl a xs))(ys : list a)(e : list_eq a xs ys), p ys e
| a nil p prefl nil unit.star := prefl
| a (cons x xs) p prefl (cons y ys) (prod.mk (Eq.mk .(x)) e) :=
  J a xs (λ zs e, p (cons x zs) (prod.mk (Eq.mk x) e)) prefl ys e
