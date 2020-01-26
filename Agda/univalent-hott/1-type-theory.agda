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

{- Not sure how to actually say this:
exercise-1-13 :
  {i : Level} {A : UU i} {x: empty}
  → ¬ (¬ (coprod A (¬ A))
exercise-1-13 = (\ f → f (ind-empty x)) -}

-- Yare, yare
-- exercise-1-15
