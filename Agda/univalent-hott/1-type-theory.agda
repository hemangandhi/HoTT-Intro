{-# OPTIONS --without-K --exact-split #-}

module 1-type-theory where

import 00-preamble
open 00-preamble public

-- Exercise 1.1 (From ../02-pi.agda)
_∘-1-1_ :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (B → C) → ((A → B) → (A → C))
(g ∘-1-1 f) a = g (f a)

import 04-inductive-types
open 04-inductive-types public

-- Exercise 1.2
recursorOfProjections :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (A → B → C) → (prod A B) → C
recursorOfProjections f p = f (pr1 p) (pr2 p)

-- Exercise 1.11 is neg-triple-neg

exercise-1-12-i : {i j : Level} {A : UU i} {B : UU j} → A → B → A
exercise-1-12-i x y = x

exercise-1-12-ii : {i : Level} {A : UU i} → A → ¬ (¬ A)
exercise-1-12-ii a = (\ f → f a)

exercise-1-12-iii :
  {i j : Level} {A : UU i} {B : UU j} → 
  (coprod (¬ A) (¬ B)) → (¬ (prod A B))
exercise-1-12-iii (inl fa) = (\ p → fa (pr1 p))
exercise-1-12-iii (inr fb) = (\ p → fb (pr2 p))

kian-ex-1-13 :
  {i : Level} {A : UU i}
  → ¬ (¬ (coprod A (¬ A)))
kian-ex-1-13 = (\ f → (\ g → f (inr g)) (\ a → f (inl a)))

import 05-identity-types
open 05-identity-types public

exercise-1-15 :
  {i j : Level} {A : UU i} (C : A → UU j) (x : A) (y : A) → (Id x y) → (C x) → (C y)
exercise-1-15 C x y eq = ind-Id x (\ y' eq' → (C(x) → C(y'))) (\ x → x) y eq
