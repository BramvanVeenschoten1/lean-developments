
-- record Stream (a : Type) where
--   head : a
--   tail : Stream a

def Stream (a : Type): Type := ℕ → a

open nat
open bool

def unfold{a s : Type}(hd : s → a)(tl : s → s): s → Stream a
| st zero := hd st
| st (succ n) := unfold (tl st) n

def head {a : Type}(xs : Stream a): a := xs zero

def tail {a : Type}(xs : Stream a): Stream a := λ n, xs (succ n)

def cons {a : Type}(x : a)(xs : Stream a) : Stream a
| zero := x
| (succ n) := xs n

theorem eta : ∀ {a : Type}(xs : Stream a), xs = cons (head xs) (tail xs) :=
begin
    intros,
    apply funext,
    intro n,
    induction n,
    refl,
    refl
end

--zipWith f xs ys := cons (f (head xs) (head ys)) (zipWith f (tail xs) (tail ys)))

def zipWith {a b c : Type}(f : a → b → c): Stream a → Stream b → Stream c
| xs ys zero := f (head xs) (head ys)
| xs ys (succ n) := zipWith (tail xs) (tail ys) n

def zipWith' {a b c : Type}(f : a → b → c)(xs : Stream a)(ys : Stream b): Stream c :=
  unfold
    (λ x, f (head (prod.fst x)) (head (prod.snd x)))
    (λ xs, prod.mk (tail (prod.fst xs)) (tail (prod.snd xs)))
    (prod.mk xs ys)

-- record colist (a : Type) where
--   isCons : bool
--   head : isCons = tt -> a
--   tail : isCons = tt -> colist a

inductive colistaux (a : Type): ℕ → Type
| nil : colistaux zero
| cons : ∀ {n}, Pi isCons : bool, (isCons = tt → a) → (isCons = tt → colistaux n) → colistaux (succ n)

def Colist (a : Type): Type := Π n : ℕ, colistaux a n

def corec {a s : Type}(iscons : s → bool)(head : Π st : s, iscons st = tt → a)(tail : Π st : s, iscons st = tt → s): s → Colist a
| st zero := colistaux.nil a
| st (succ n) := colistaux.cons (iscons st) (head st) (λ p, corec (tail st p) n)

--def isCons {a : Type}: Colist a → bool
--def head' {a : Type}

