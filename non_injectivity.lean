
inductive I (F : Type → Prop): Type
| mk : I

axiom inj : ∀ {x y}, I x = I y → x = y

def P (x : Type) : Prop := (∀ (a : Type → Prop), x = I a → (a x → false) → false) → false

def not_pip (H : P (I P)): false :=
  H (λ a e not_ap, not_ap (eq.subst (inj e) H))

def contradiction : false :=
  not_pip (λ f, f P (eq.refl (I P)) not_pip)
