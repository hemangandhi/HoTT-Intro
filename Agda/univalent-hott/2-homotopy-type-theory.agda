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
