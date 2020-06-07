{-# OPTIONS --without-K --exact-split --cubical #-}

-- This is unfortunate, but Arch doesn't have the cubical stuff
-- in the stdlib package it comes with (and cabal on Arch is
-- significantly worse).
open import Agda.Builtin.Cubical.Id
open import Agda.Builtin.Cubical.Path

open import Agda.Builtin.List
open import Agda.Builtin.Bool

-- I understand it better calling stuff "UU" from Egbert's notes.
open import 00-preamble
-- Same for + types -- too lazy to find the builtin
open import 04-inductive-types

-- https://dl.acm.org/doi/pdf/10.1145/3341691 page 11
-- set quotient (truncate the quotient)
-- ≡ is from Agda.Builtin.Id
data Quot {i : Level} (A : UU i) (R : A → A → UU i): UU i where
  cls : A → Quot A R
  eq : (a b : A) → (r : R a b) → (cls a) ≡ (cls b)
  trunc : (x y : Quot A R) → (p q : x ≡ y) → p ≡ q

-- First definition of a group: List(A + A) / R. Some oddity:
-- 1) f : A → A → Bool is an equality predicate (Eq in Haskell), but I'm not sure how to
--    insist that (f a₁ a₂ = true) ≅ (a₁ = a₂) or just say "if the identity type is
--    inhabited." Also encode-decode seems to use information from the type, so defining
--    f should be a reasonable requirement (it's just code, but using true for 𝟙 and false
--    for 𝟘).
-- 2) I promise it terminates. Otherwise it insists that the first recursive call is
--    uncertain but the list is clearly one element shorter.
-- 3) I think the warning isn't all that important (but I'm a programmer, don't trust me).
--    My understanding is that the warning means "the definitional equalities Agda has can
--    be surprising" but I don't see how it's bad yet.
{-# TERMINATING #-}
cancelList : {i : Level} {A : UU i} (eq : A → A → Bool) (l : List (coprod A A)) → List (coprod A A)
cancelList e [] = []
cancelList e ((inl a₁) ∷ (inr a₂) ∷ xs) with e a₁ a₂
...                                      | true = cancelList e xs
...                                      | false = (inl a₁) ∷ (cancelList e ((inr a₂) ∷ xs))
cancelList e ((inr a₁) ∷ (inl a₂) ∷ xs) with e a₁ a₂
...                                      | true = cancelList e xs
...                                      | false = (inr a₁) ∷ (cancelList e ((inl a₂) ∷ xs))
cancelList e (x ∷ xs) = x ∷ (cancelList e xs)


