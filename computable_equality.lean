-- notes
-- There are 2 ways to compute an equality:
-- 1. defining a binary function returning bool, coercing the result to Prop
--   pros:
--   - immediate usability
--   - easy decidability proof
--   - easy proof of K
-- 2. defining a function returning prop directly, using large elimination
--   pros:
--   - easy definition of refl
--   - easy definition of J
--   - easy proofs by simple pattern matching (for constructors taking 2 or more arguments)
-- neither method is suitable for defining equalities on dependent parametrized types,
-- such as parametric dependent pairs.
-- both are easily proven equivalent to each other and to standard equality

inductive foo : Type
| leaf : foo
| node : foo → foo → foo

inductive void : Type

open foo
open bool

def foo_eq : foo → foo → bool
| leaf leaf := tt
| (node l1 r1) (node l2 r2) := foo_eq l1 l2 && foo_eq r1 r2
| _ _ := ff

def foo_Eq : foo → foo → Type
| leaf leaf := unit
| (node l1 r1) (node l2 r2) := foo_Eq l1 l2 × foo_Eq r1 r2
| _ _ := void

def b2t : bool → Type
| tt := unit
| ff := void

def L1 : ∀ x y : bool, b2t (x && y) → b2t x × b2t y
| tt tt () := ((), ())

def L2 : ∀ x y : bool, b2t x → b2t y → b2t (x && y)
| tt tt () () := ()

def T1 : ∀ x y : foo, b2t (foo_eq x y) → foo_Eq x y
| leaf leaf () := ()
| (node l1 r1) (node l2 r2) e :=
  let (el, er) := L1 (foo_eq l1 l2) (foo_eq r1 r2) e in
    (T1 l1 l2 el, T1 r1 r2 er)

def T2 : ∀ x y : foo, foo_Eq x y → b2t (foo_eq x y)
| leaf leaf () := ()
| (node l1 r1) (node l2 r2) (el, er) := L2 _ _ (T2 l1 l2 el) (T2 r1 r2 er)

def irrelevant : ∀ (x : bool)(e1 e2 : b2t x)(P : b2t x → Type), P e1 → P e2
| tt () () p prefl := prefl

def foo_refl : ∀ x : foo, b2t (foo_eq x x)
| leaf := ()
| (node l r) := L2 _ _ (foo_refl l) (foo_refl r)

def foo_Refl : ∀ x : foo, foo_Eq x x
| leaf := ()
| (node l r) := (foo_Refl l, foo_Refl r)

def J1 : ∀ (x y : foo)(P : ∀ z : foo, b2t (foo_eq x z) → Type)(e : b2t (foo_eq x y)), P x (foo_refl x) → P y e
| leaf leaf P () prefl := prefl
| (node l1 r1) (node l2 r2) P e prefl :=
  @prod.rec (b2t (foo_eq l1 l2)) (b2t (foo_eq r1 r2)) (λ _, P (node l2 r2) e) (λ el er,
  let P2  := J1 _ _ (λ z e, P (node z r1) (L2 _ _ e (foo_refl r1))) el prefl in
  let P3  := J1 _ _ (λ z e, P (node l2 z) (L2 _ _ el e)) er P2 in
    irrelevant _ _ e (P (node l2 r2)) P3
    ) (L1 _ _ e)

def J2 : ∀ (x y : foo)(P : ∀ z : foo, foo_Eq x z → Type)(e : foo_Eq x y), P x (foo_Refl x) → P y e
| leaf leaf P () prefl := prefl
| (node l1 r1) (node l2 r2) P (el, er) prefl :=
  let P2 := J2 _ _ (λ z e, P (node z r1) (e, (foo_Refl r1))) el prefl in
            J2 _ _ (λ z e, P (node l2 z) (el, e)) er P2

def K : ∀ (x : foo)(P : foo_Eq x x → Type)(e : foo_Eq x x), P (foo_Refl x) → P e
| leaf P () prefl := prefl
| (node l r) P (le, re) prefl :=
  let prefl2 := K _ (λ z, P (z, foo_Refl r)) le prefl  in
                K _ (λ z, P (le, z)) re prefl2

def neg (p : Type): Type := p → void

def Dec(p : Type): Type := sum p (neg p)

open sum

def dec_bool : ∀ x : bool, Dec (b2t x)
| tt := inl ()
| ff := inr (λ x, x)

def dec_eq1 (x y : foo): Dec (b2t (foo_eq x y)) := dec_bool (foo_eq x y)

def dec_eq2 : ∀ x y : foo, Dec (foo_Eq x y)
| leaf leaf := inl ()
| leaf (node l r) := inr (λ x, x)
| (node l r) leaf := inr (λ x, x)
| (node l1 r1) (node l2 r2) :=
    match dec_eq2 l1 l2, dec_eq2 r1 r2 with
    | (inr x), _       := inr (λ y, x (prod.fst y))
    | (inl x), (inl y) := inl (x, y)
    | (inl x), (inr y) := inr (λ x, y (prod.snd x))
    end

section foo
variables
  (a : Type)
  (a_eq : a → a → Type)
  (a_refl : ∀ x : a, a_eq x x)
  (a_J : ∀ (x y : a)(P : ∀ z : a, a_eq x z → Type)(e : a_eq x y), P x (a_refl x) → P y e)
  (b : a → Type)
  (b_eq : ∀ x : a, b x → b x → Type)
  (b_refl : ∀ (x : a)(y : b x), b_eq x y y)
  (b_J : ∀ (x : a)(y z : b x)(P : ∀ z : b x, b_eq x y z → Type)(e : b_eq x y z), P y (b_refl x y) → P z e)

inductive dpair
| mk : ∀ x : a, b x → dpair

def dpair_Eq : dpair a b → dpair a b → Type
| (dpair.mk x1 y1) (dpair.mk x2 y2) := dpair (a_eq x1 x2) (λ e, b_eq x2 (a_J x1 x2 (λx e, b x) e y1) y2)

-- undefinable
variable dpair_Refl : ∀ p : dpair a b, dpair_Eq a a_eq a_refl a_J b b_eq p p

end foo

