{-# OPTIONS --without-K --exact-split #-}

module 1-type-theory where

import 00-preamble
open 00-preamble public

-- Exercise 1.1 (From ../02-pi.agda)
_∘_ :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (B → C) → ((A → B) → (A → C))
(g ∘ f) a = g (f a)

-- Exercise 1.2 -- pre-requisites: defining products (by projections)
record Prod {i j : Level} (A : UU i) (B : UU j) : UU (i ⊔ j) where
  constructor _x_
  field
    projOne : A
    projTwo : B
open Prod public

-- The actual exercise 1.2: rec_{A x B} from the above.
recursorProd : {i j k : Level} (A : UU i) (B : UU j) (C : UU k) →
                (A → B → C) → (Prod A B) → C
recursorProd f p = f (projOne p) (projTwo p)
  where open Prod p
