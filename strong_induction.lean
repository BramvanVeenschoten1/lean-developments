
def conflict {a : Prop}(e : bool.ff = bool.tt): a :=
    cast (@congr_arg _ Prop _ _ (@bool.rec (λ _, Prop) true a) e) trivial

def is_lt : ordering → bool :=
    @ordering.rec (λ _, bool) bool.tt bool.ff bool.ff

def compare : ℕ → ℕ → ordering :=
    @nat.rec (λ _, ℕ → ordering)
        (@nat.rec (λ _, ordering)
            ordering.eq
            (λ _ _, ordering.lt))
        (λ _ ih, @nat.rec (λ _, ordering)
            ordering.gt
            (λ m _, ih m))

def less (n m : ℕ): Prop := compare n m = ordering.lt

def leq(n m : ℕ): Prop := less n (nat.succ m)

def less_than_succ : ∀ n, less n (nat.succ n) :=
    @nat.rec
        (λ n, less n (nat.succ n))
        (eq.refl ordering.lt)
        (λ _ ih, ih)

def not_less_than_zero {a} : ∀ {n}, less n nat.zero → a :=
    @nat.rec
        (λ n, less n nat.zero → a)
        (λ l, conflict (congr_arg is_lt l))
        (λ _ _ l, conflict (congr_arg is_lt l))

def or_bimap {a b c d : Prop}(f : a → c)(g : b → d): a ∨ b → c ∨ d :=
    or.rec
        (λ l, or.intro_left _ (f l))
        (λ r, or.intro_right _ (g r))

def leq_is_less_or_eq : ∀ (n m : ℕ), leq n m → (n = m) ∨ less n m :=
    @nat.rec
        (λ z, ∀ m : ℕ, leq z m → (z = m) ∨ less z m)
        (@nat.rec
            (λ z, leq nat.zero z → (nat.zero = z) ∨ less nat.zero z)
            (λ _, or.intro_left _ (eq.refl _))
            (λ _ _ _, or.intro_right _ (eq.refl _)))
        (λ y ih, @nat.rec
            (λ z, leq (nat.succ y) z → (nat.succ y = z) ∨ less (nat.succ y) z)
            not_less_than_zero
            (λ z _ l1, 
                or_bimap
                    (congr_arg nat.succ)
                    (λ x, x)
                    (ih z l1)))

def strong(p : ℕ → Prop)(h : ∀ x : ℕ, (∀ y : ℕ, less y x → p y) → p x): ∀ (n m : ℕ), less m n → p m :=
    @nat.rec
        (λ z, ∀ m : ℕ, less m z → p m)
        (λ _ , not_less_than_zero)
        (λ n ih m l,
            or.rec
                (λ e, eq.subst (eq.symm e) (h n ih))
                (ih m)
                (leq_is_less_or_eq m n l))

def strong_induction(p : ℕ → Prop)(h : ∀ x : ℕ, (∀ y : ℕ, less y x → p y) → p x)(n : ℕ): p n :=
    strong p h (nat.succ n) n (less_than_succ n)

#reduce strong_induction
