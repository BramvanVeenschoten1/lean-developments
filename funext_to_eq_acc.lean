
inductive Acc (a : Type)(r : a → a → Type): a → Type
| intro : ∀ x : a, (∀ y : a, r y x → Acc y) → Acc x

def Acc_case
  (a : Type)
  (r : a → a → Type)
  (x : a)
  (p : Acc a r x → Prop)
  (b : ∀ (inv : ∀ y : a, r y x → Acc a r y), p (Acc.intro x inv))
  (ac : Acc a r x):
    p ac
  :=
    @Acc.rec a r (λ x ac1, ∀ 
        (p : Acc a r x → Prop)
        (b : ∀ (inv : ∀ y : a, r y x → Acc a r y), p (Acc.intro x inv)), p ac1)
    (λ x inv ih p b, b inv) x ac p b

def foo (a : Type)(r : a → a → Type): ∀ (x : a)(ac1 ac2 : Acc a r x), ac1 = ac2 :=
  @Acc.rec a r (λ x ac1, ∀ ac2 : Acc a r x, ac1 = ac2)
    (λ x inv ih ac2,
      @Acc_case a r x (λ ac2, Acc.intro x inv = ac2)
        (λinv2, 
        let T0 := λ (y : a)(l : r y x), ih y l (inv2 y l) in
        let T1 := λ y, @funext (r y x) (λ _, Acc a r y) (inv y) (inv2 y) in
        let T3 := @funext a (λ z, r z x → Acc a r z) inv inv2 (λ z, T1 z (T0 z)) in
        let T4 := @eq.subst (∀ y : a, r y x → Acc a r y) (λ i, Acc.intro x inv = Acc.intro x i) inv inv2 T3 (eq.refl _) in
          begin exact T4 end) ac2)
