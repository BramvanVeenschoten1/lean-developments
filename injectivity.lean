inductive Eq (a : Type)(x : a): a → Type
| refl : Eq x

def sub{a : Type}{x : a}(p : a → Type)(pr : p x){y : a}(e : Eq a x y): p y :=
  @Eq.rec a x (λ z _, p z) pr y e

inductive dpair(a : Type)(b : a → Type): Type
| mk : ∀ x, b x → dpair

open dpair

variables
  {a : Type}
  {b : a → Type}

def proj1 : dpair a b → a :=
  @dpair.rec a b (λ _, a) (λ x y, x)

def proj2 : ∀ p : dpair a b, b (proj1 p) :=
  @dpair.rec a b (λ p, b (proj1 p)) (λ x y, y)

def no_conf_t (p1 p2 : dpair a b): Type :=
  dpair (Eq a (proj1 p1) (proj1 p2)) (λ e, Eq (b (proj1 p2)) (sub b (proj2 p1) e) (proj2 p2))

def no_conf_r : ∀ p : dpair a b, no_conf_t p p :=
  @dpair.rec a b (λ p, no_conf_t p p) (λ x y, mk (Eq.refl x) (Eq.refl y))

def no_conf (p1 p2 : dpair a b): Eq (dpair a b) p1 p2 → no_conf_t p1 p2 :=
  sub (λ p, no_conf_t p1 p) (no_conf_r p1)

def mk_injective (x1 x2 : a)(y1 : b x1)(y2 : b x2): Eq (dpair a b) (mk x1 y1) (mk x2 y2) → dpair (Eq a x1 x2) (λ e, Eq (b x2) (sub b y1 e) y2) :=
  no_conf (mk x1 y1) (mk x2 y2)

inductive mpair(a : Type)(b : a → Type): Type
| no : mpair
| yes : ∀ x, b x → mpair

open mpair

def yes_injective (x1 x2 : a)(y1 : b x1)(y2 : b x2): Eq (mpair a b) (yes x1 y1) (yes x2 y2) → dpair (Eq a x1 x2) (λ e, Eq (b x2) (sub b y1 e) y2) :=
    let proj1 : mpair a b → a :=
      @mpair.rec a b (λ _, a) x1 (λ x y, x) in
    let proj2 : ∀ p : mpair a b, b (proj1 p) :=
      @mpair.rec a b (λ p, b (proj1 p)) y1 (λ x y, y) in
    let no_conf_t (p1 p2 : mpair a b): Type :=
      dpair (Eq a (proj1 p1) (proj1 p2)) (λ e, Eq (b (proj1 p2)) (sub b (proj2 p1) e) (proj2 p2)) in
    let no_conf_r : ∀ p : mpair a b, no_conf_t p p :=
      @mpair.rec a b (λ p, no_conf_t p p) (mk (Eq.refl x1) (Eq.refl y1)) (λ x y, mk (Eq.refl x) (Eq.refl y)) in
    let no_conf (p1 p2 : mpair a b): Eq (mpair a b) p1 p2 → no_conf_t p1 p2 :=
      sub (λ p, no_conf_t p1 p) (no_conf_r p1) in
    no_conf (yes x1 y1) (yes x2 y2)

