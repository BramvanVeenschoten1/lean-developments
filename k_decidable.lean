-- Live javascript version of Lean

section deceq

variable {a : Type}

inductive Void : Type

def void {a : Type} : Void → a := @Void.rec (λ _, a)

def Not (a : Type): Type := a → Void

inductive Eq (x : a): a → Type
| Refl : Eq x

def Subst {x y : a}(p : a → Type)(pr : p x)(e : Eq x y): p y :=
    Eq.rec pr e

def cong {b}(f : a → b): ∀ {x y : a}, Eq x y → Eq (f x) (f y)
| x .(x) (Eq.Refl .(x)) := Eq.Refl (f x)

def comp : ∀ {x y z : a}, Eq x y → Eq x z → Eq y z
| x .(x) .(x) (Eq.Refl .(x)) (Eq.Refl .(x)) := Eq.Refl x

def trans_sym_eq : ∀ {x y : a}(u : Eq x y), Eq (comp u u) (Eq.Refl y)
| x .(x) (Eq.Refl .(x)) := Eq.Refl (Eq.Refl x)

inductive Either (a b : Type): Type
| Left  : a → Either
| Right : b → Either

def dec (a : Type): Type := Either a (Not a)

def nu {x y : a}(f : dec (Eq x y))(e : Eq x y): Eq x y :=
  Either.rec
    (λ e2, e2)
    (λ e2, void (e2 e))
    f

def nu_const {x y : a}: ∀ (f : dec (Eq x y))(u v : Eq x y), Eq (nu f u) (nu f v) :=
    @Either.rec _ _ (λ e, ∀ (u v : Eq x y), Eq (nu e u) (nu e v))
        (λ e u v, Eq.Refl _)
        (λ e u v, void (e u))

variable f : ∀ (x y : a), dec (Eq x y)

def nu_inv {x y : a}(v : Eq x y): Eq x y := comp (nu (f x x) (Eq.Refl x)) v

def nu_left_inv : ∀ {x y : a}(u : Eq x y), Eq (nu_inv f (nu (f x y) u)) u :=
begin
    intros,
    cases u,
    unfold nu_inv,
    unfold nu,
    apply trans_sym_eq
end

def uip {x y : a}(p1 p2 : Eq x y) : Eq p1 p2 :=
    let T0 : Eq (nu (f x y) p1) (nu (f x y) p2) := nu_const (f x y) p1 p2 in
    let T1 : Eq (nu_inv f (nu (f x y) p1)) (nu_inv f (nu (f x y) p2)) := cong (nu_inv f) T0 in
    let T2 := @nu_left_inv a f x y p1 in
    let T3 := @Subst (Eq x y) (nu_inv f (nu (f x y) p1)) p1 (λ p, Eq p (nu_inv f (nu (f x y) p2))) T1 T2 in
    let T4 := @nu_left_inv a f x y p2 in
    let T5 := @Subst (Eq x y) (nu_inv f (nu (f x y) p2)) p2 (Eq p1) T3 T4 in
        T5

def k_dec {x : a}(f : ∀ x y, dec (Eq x y))(p : Eq x x → Type)(p1 : p (Eq.Refl x))(e : Eq x x): p e :=
    @Subst (Eq x x) (Eq.Refl x) e p p1 (@uip a f x x (Eq.Refl x) e)

def nat_eq : ℕ → ℕ → bool
| nat.zero nat.zero := bool.tt
| nat.zero (nat.succ m) := bool.ff
| (nat.succ n) nat.zero := bool.ff
| (nat.succ n) (nat.succ m) := nat_eq n m

def Nat_eq (n m : ℕ): Type := Eq (nat_eq n m) bool.tt

def Nat_eq_refl : ∀ n, Nat_eq n n := @nat.rec (λ n, Nat_eq n n) (Eq.Refl _) (λ _ ih, ih)

def left : ∀ {n m : ℕ}, Nat_eq n m → Eq n m
| nat.zero nat.zero x := Eq.Refl _
| (nat.succ n) (nat.succ m) x := cong nat.succ (@left n m x)

def right {n m : ℕ}(e : Eq n m): Nat_eq n m :=
    Subst _ (Nat_eq_refl n) e

def nat_dec (n m : ℕ): dec (Eq n m) :=
    @bool.rec (λ b, Eq (nat_eq n m) b → dec (Eq n m))
        (λ x, Either.Right _ (λ e : Eq n m, begin cases comp x (right e) end))
        (λ x, Either.Left _  (left x)) (nat_eq n m) (Eq.Refl _)

def k_nat {n : ℕ} : ∀ (p : Eq n n → Type)(pr : p (Eq.Refl n))(e : Eq n n), p e :=
    k_dec nat_dec

#reduce k_nat (λ x, bool) bool.tt (Eq.Refl 10)

end deceq




