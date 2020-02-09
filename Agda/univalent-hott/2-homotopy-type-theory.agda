{-# OPTIONS --without-K --exact-split #-}

import 05-identity-types
open 05-identity-types public

-- Inversion is uninteresting and comes from:
inversion-proof :
  {i : Level} {A : UU i} (x : A) → (y : A) → Id x y → Id y x
inversion-proof x y = ind-Id x (λ y' p' → Id y' x) refl y

lemma-2-2-2-i :
  {i j : Level} {A : UU i} {B : UU j} (x y z : A) (f : A → B) → (p : Id x y) → (q : Id y z)
  → Id (ap f (p ∙ q)) ((ap f p) ∙ (ap f q))
lemma-2-2-2-i x y z f refl q = refl
-- We apparently don't need a second induction on q..

lemma-2-2-2-ii :
  {i j : Level} {A : UU i} {B : UU j} (x y : A) (f : A → B) → (p : Id x y)
  → Id (ap f (inv p)) (inv (ap f p))
lemma-2-2-2-ii x y f refl = refl

lemma-2-2-2-iii :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (x y : A) (f : A → B) → (g : B → C) → (p : Id x y)
  → Id (ap g (ap f p)) (ap (g ∘ f) p)
lemma-2-2-2-iii x y f g refl = refl

lemma-2-2-2-iv :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (x y : A) → (p : Id x y)
  → Id (ap (λ x → x) p) p
lemma-2-2-2-iv x y refl = refl

-- Path lifting property
lemma-2-3-2 :
  {i j : Level} {A : UU i} {P : A → UU j} (x y : A) (u : P x) → (p : Id x y)
  → Id (pair x u) (pair y (tr P p u))
lemma-2-3-2 x y u refl = refl

lemma-2-3-9 :
  {i j : Level} {A : UU i} {P : A → UU j} (x y z : A) (u : P x) → (p : Id x y)
  → (q : Id y z) → Id (tr P q (tr P p u)) (tr P (p ∙ q) u)
lemma-2-3-9 x y z u refl q = refl

lemma-2-3-10 :
  {i j k : Level} {A : UU i} {B : UU j} {P : B → UU k} (x y : A) (f : A → B) (u : P (f x)) → (p : Id x y)
  → Id (tr (P ∘ f) p u) (tr P (ap f p) u)
lemma-2-3-10 x y f u refl = refl

lemma-2-3-11 :
  {i j k : Level} {A : UU i} {P : A → UU j} {Q : A → UU k}
  (x y : A) (f : (z : A) → P z → Q z) (u : P x) → (p : Id x y)
  → Id (tr Q p (f x u)) (f y (tr P p u))
lemma-2-3-11 x y f u refl = refl

-- Eckert-Hamilton

-- First, the loop
loop-type : {i : Level} {A : UU i} (x : A) → UU i
loop-type x = Id x x

order-2-star : 
  {i : Level} {A : UU i} (a b c : A) → (p q : Id a b) → (r s : Id b c)
   → (alpha : Id p q) → (beta : Id r s) → Id (concat p c r) (concat q c s)
order-2-star a b c refl q refl s refl refl = refl

left-whisker :
  {i : Level} {A : UU i} (a b c : A) → (p q : Id a b) → (r : Id b c)
   → (alpha : Id p q) → Id (concat p c r) (concat q c r)
left-whisker a b c refl refl r refl = refl

right-whisker :
  {i : Level} {A : UU i} (a b c : A) → (p : Id a b) → (r s : Id b c)
   → (beta : Id r s) → Id (concat p c r) (concat p c s)
right-whisker a b c p refl refl refl = refl

-- TODO: Eckmann Hilton

-- 2.4: the equivalence of functions, quasi-inverses

-- `Sim-By` might be poorly set up since it basically takes the witness of what it
-- actually should just be. (../07- has the correct stuff.)
data Fn-Equiv {i j : Level} (A : UU i) (B : UU j) (f g : A → B) : UU (i ⊔ j) where
  Sim-By : ((x : A) → (Id (f x) (g x))) → Fn-Equiv A B f g

-- 2.6.1
product-functoriality :
  {i j : Level} {A : UU i} {B : UU j} (x y : prod A B) → (Id x y)
  → (prod (Id (pr1 x) (pr1 y)) (Id (pr2 x) (pr2 y)))
product-functoriality x y refl = pair refl refl

-- 2.6.2
pair= :
  {i j : Level} {A : UU i} {B : UU j} (a₁ a₂ : A) → (b₁ b₂ : B)
  → (prod (Id a₁ a₂) (Id b₁ b₂)) → (Id (pair a₁ b₁) (pair a₂ b₂))
pair= a₁ a₂ b₁ b₂ (pair refl refl) = refl

-- This is a bit of laziness to exhibit both bits of the proof with the same a₁ etc.
-- The point is to show that product-functoriality and pair= are quasi-inverses.
functoriality-is-equiv-to-2-6-2 :
  {i j : Level} {A : UU i} {B : UU j} {a₁ a₂ : A} {b₁ b₂ : B} →
  -- First two bindings give us shorthands for the proper invocations of the above
  -- functions (currying away aₙ and bₙ).
  let functorial = (product-functoriality (pair a₁ b₁) (pair a₂ b₂))
      2-6-2 = (pair= a₁ a₂ b₁ b₂)
      thm-after-funct = (Fn-Equiv (prod (Id a₁ a₂) (Id b₁ b₂))
                                  (prod (Id a₁ a₂) (Id b₁ b₂))
                                  (λ x → x)
                                  (functorial ∘ 2-6-2))
      funct-after-thm = (Fn-Equiv (Id (pair a₁ b₁) (pair a₂ b₂))
                                  (Id (pair a₁ b₁) (pair a₂ b₂))
                                  (2-6-2 ∘ functorial)
                                  (λ x → x))
  in (prod thm-after-funct funct-after-thm)
functoriality-is-equiv-to-2-6-2 = pair (Sim-By (λ {(pair refl refl) → refl})) (Sim-By (λ {refl → refl}))

-- 2.6.4
pair-transport :
  {i j k : Level} {Z : UU k} {A : Z → UU i} {B : Z → UU j} (z w : Z) → (p : Id z w) → (x : prod (A z) (B z))
  → (Id (tr (λ z → (prod (A z) (B z))) p x) (pair (tr A p (pr1 x)) (tr B p (pr2 x))))
pair-transport z w refl (pair az bz) = refl

-- 2.6.5
ap-functorial :
  {i j k l : Level} {A : UU i} {A' : UU j} {B : UU k} {B' : UU l} (g : A → A') → (h : B → B')
  → (x y : prod A B) → (p : Id (pr1 x) (pr1 y)) → (q : Id (pr2 x) (pr2 y)) →
  let pf= = (pair= (pr1 x) (pr1 y) (pr2 x) (pr2 y))
      pgh = (pair= (g (pr1 x)) (g (pr1 y)) (h (pr2 x)) (h (pr2 y)))
      f = (λ x → pair (g (pr1 x)) (h (pr2 x)))
  in Id (ap f (pf= (pair p q))) (pgh (pair (ap g p) (ap h q)))
ap-functorial g h (pair aₓ bₓ) (pair ay by) refl refl = refl
