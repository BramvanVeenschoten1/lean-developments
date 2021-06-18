inductive foo : Type
| Z : foo
| S : ℕ → foo 

def bar : ℕ → foo
| nat.zero := foo.Z
| (nat.succ n) := foo.S n

inductive facc : foo → Type
| intro : ∀ x : foo, (∀ n : ℕ, x = foo.S n → facc (bar n)) → facc x

def flen : ∀ x : foo, facc x → ℕ :=
  @facc.rec (λ x acx, ℕ) (
    @foo.rec (λ x, (Π n : ℕ, x = foo.S n → facc (bar n)) → (Π n : ℕ, x = foo.S n → ℕ) → ℕ)
      (λ _ _, nat.zero)
      (λ n _ ih, ih n (eq.refl _)))

def fac_Z : facc foo.Z :=
  begin
    apply facc.intro,
    intro n,
    intro e,
    cases e,
  end

def fac_S : ∀ n : ℕ, facc (bar n) → facc (foo.S n) :=
  begin
    intro,
    intro,
    apply facc.intro,
    intro m,
    intro e,
    cases e,
    exact a,
  end
