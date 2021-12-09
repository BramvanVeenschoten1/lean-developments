open bool

universes u v w

inductive Unit : Type u
| Star : Unit

open Unit

inductive Void : Type u

inductive Box (p : Prop): Type u
| Mk : p → Box

def Absurd{A : Type u}: Void → A := @Void.rec (λ _, A)

inductive W (A : Type u)(B : A → Type v): Type (max u v)
| Node : Π x : A, (B x → W) → W

open W

inductive Sigma (A : Type u)(B : A → Type v): Type (max u v)
| Mk : Π x : A, B x → Sigma

open Sigma

def p1 (A : Type u)(B : A → Type v): Sigma A B → A
| (Mk x y) := x

def p2(A : Type u)(B : A → Type v): Π p : Sigma A B, B (p1 A B p)
| (Mk x y) := y

def AccF (A : Type u)(R : A → A → Type v): A → Type* :=
  λ x, Sigma A (λ y, R y x)

def Sacc (A : Type u)(R : A → A → Type v): Type* :=
  W A (AccF A R)

#check @W.rec

def Sacc_rec (A : Type u)(R : A → A → Type v)(C : Type w)(h : Π x : A, (Π y : A, R y x → C) → C): Π a : Sacc A R, C :=
  @W.rec A (AccF A R) (λ _, C) (λ x pred ih, h x (λ y l, ih (Mk y l)))

-- the predicate states, recursively, that the index is equal to the data node
def AccP (A : Type u)(R : A → A → Type v): Sacc A R → A → Type* :=
  Sacc_rec A R _ (λ x ih y, Box (x = y) × Π (z : A)(l : R z x), ih z l z) 

def Lemma
  (A : Type u)
  (R : A → A → Type v)
  (x : A)
  (pred : AccF A R x → Sacc A R):
  (@Sigma.rec A (λ y, R y x) (λ_, Sacc A R) (λi j, pred (Mk i j))) = pred
  :=
begin
    apply funext,
    intro p,
    cases p,
    refl,
end

def Sacc_ind
  (A : Type u)
  (R : A → A → Type v)
  (C : Sacc A R → Type w)
  (h : Π 
    (x : A)
    (pr : Π y : A, R y x → Sacc A R),
    (Π (y : A)(l : R y x), C (pr y l)) →
    C (Node x (@Sigma.rec A (λ y, R y x) (λ _, Sacc A R) pr)))
    : Π sac : Sacc A R, C sac
   := 
  @W.rec A (AccF A R) C (λx pred ih,
     @eq.rec
      (AccF A R x → Sacc A R)
      (@Sigma.rec A (λy, R y x) (λ_, Sacc A R) (λ i j, pred (Mk i j)))
      (λf, C (Node x f))
      (h x (λ y l, pred (Mk y l)) (λ y l, ih (Mk y l)))
      pred
      (Lemma A R x pred))

def rec0
  (A : Type u)
  (R : A → A → Type v)
  (P : A → Type w)
  (h : Π x : A, (Π y : A, R y x → P y) → P x):
  Π (sac : Sacc A R)
    (x : A),
    AccP A R sac x →
    P x :=
    Sacc_ind A R (λ sac, Π x : A, AccP A R sac x → P x) (λ x pr y z acp, begin end)
   

def Acc (A : Type u)(R : A → A → Type v)(x : A) :=
  Sigma (Sacc A R) (λ a, AccP A R a x)


