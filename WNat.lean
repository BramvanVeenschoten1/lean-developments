open bool

universes u v

inductive W (A : Type u)(B : A → Sort v): Type (max u v)
| Node : Π x : A, (B x → W) → W

open W

def NatR : bool → Prop := @bool.rec (λ _, Prop) false true

def Nat : Type := W bool NatR

def Zero : Nat := Node ff (@false.rec (Nat))

def Succ (n : Nat): Nat := Node tt (λ _, n)

def Lemma_Z(f : false → Nat): Zero = Node ff f :=
  congr_arg (@Node bool NatR ff) (funext (λ x, @false.rec _ x))

def Lemma_S(f : true → Nat):  Succ (f trivial) = Node tt f :=
  congr_arg (@Node bool NatR tt) (funext (λ x, eq.refl _))

def Nat_ind (P : Nat → Sort u)(pz : P Zero)(ps : Π n : Nat, P n → P (Succ n)): Π n : Nat, P n :=
  @W.rec bool NatR P
    (@bool.rec (λ b, Π f : (NatR b → Nat), (Π a : NatR b, P (f a)) → P (Node b f))
      (λ f _,  @eq.rec Nat Zero P pz (Node ff f) (Lemma_Z f))
      (λ f ih, @eq.rec Nat (Succ (f trivial)) P (ps (f trivial) (ih trivial)) (Node tt f) (Lemma_S f)))

def Nat_rec {C : Sort u}: C → (Nat → C → C) → Nat → C :=
  Nat_ind (λ x, C)

def Twice : Nat → Nat := Nat_rec Zero (λ p ih, Succ (Succ ih))

def from_ℕ : ℕ → Nat := @nat.rec (λ _, Nat) Zero (λ _ ih, Succ ih)

def to_ℕ : Nat → ℕ := Nat_rec nat.zero (λ _ ih, nat.succ ih)

def Leq : Nat → Nat → Prop :=
  Nat_rec
    (λ _, true)
    (λ n recur,
      Nat_rec
        false
        (λ m _, recur m))

def Leq_refl : Π n : Nat, Leq n n :=
  Nat_ind (λ n, Leq n n) trivial (λ n ih, ih)

def Less (n m : Nat): Prop := Leq (Succ n) m

def Leq_trans : Π x y z : Nat, Leq x y → Leq y z → Leq x z :=
  let P := λ x y z, Leq x y → Leq y z → Leq x z in
  Nat_ind (λ x, Π y z : Nat, P x y z)
    (λ y z l1 l2, trivial)
    (λ x ih, 
      Nat_ind (λ y, Π z : Nat, P (Succ x) y z)
        (λ z, false.rec _)
        (λ y _, 
          Nat_ind (P (Succ x) (Succ y))
          (λ _, false.rec _)
          (λ z _ l1 l2, ih y z l1 l2)))

def strong_aux (P : Nat → Type u)(h : Π x : Nat, (Π y : Nat, Less y x → P y) → P x): Π n m : Nat, Less m n → P m :=
  Nat_ind (λ n, Π m : Nat, Less m n → P m)
    (λ m, false.rec _)
    (λ n ih m l1, h m (λ y l2, ih y (Leq_trans (Succ y) m n l2 l1)))

def strong_induction(P : Nat → Type u)(h : Π x : Nat, (Π y : Nat, Less y x → P y) → P x)(n : Nat): P n :=
  strong_aux P h (Succ n) n (Leq_refl (Succ n))

#reduce to_ℕ (Twice (from_ℕ 10))
#reduce from_ℕ 10
