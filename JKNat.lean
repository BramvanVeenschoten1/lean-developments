inductive void : Type

def Eq : ℕ → ℕ → Type :=
  @nat.rec (λ _, ℕ → Type)
    (@nat.rec (λ _, Type)
      unit
      (λ _ _, void))
    (λ _ ih, @nat.rec (λ _, Type)
      void
      (λ m _, ih m))

def Refl : ∀ n : ℕ, Eq n n :=
  @nat.rec (λ n, Eq n n) unit.star (λ _ ih, ih)

def J : ∀ (n : ℕ)(P : ∀ m : ℕ, Eq n m → Type)(prefl : P n (Refl n))(m : ℕ)(e : Eq n m), P m e :=
  @nat.rec (λ n, Π (P : ∀ m : ℕ, Eq n m → Type)(prefl : P n (Refl n))(m : ℕ)(e : Eq n m), P m e)
    (λ P prefl, @nat.rec (λ m, Π e : Eq nat.zero m, P m e) 
      (@punit.rec (P 0) prefl)
      (λ m _, @void.rec (λ e, P (nat.succ m) e)))
    (λ n ih P prefl, @nat.rec (λ m, Π e : Eq (nat.succ n) m, P m e)
      (λ e, @void.rec (λ _, P nat.zero e) e)
      (λ m _ e, ih (λ k e, P (nat.succ k) e) prefl m e))
 
def K : ∀ (n : ℕ)(P : Eq n n → Type)(prefl : P (Refl n))(e : Eq n n), P e :=
  @nat.rec (λ n, ∀(P : Eq n n → Type)(prefl : P (Refl n))(e : Eq n n), P e)
    (λ p prefl, @punit.rec p prefl)
    (λ n ih p prefl, ih p prefl)
