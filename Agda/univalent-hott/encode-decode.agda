{-# OPTIONS --without-K --exact-split #-}

module encode-decode where

import 05-identity-types
open 05-identity-types public

record Lift {i j : Level} (A : UU i) : UU (i ⊔ j) where
  field
    raise : A

module Coprod where
  code-left : {i j : Level} {A : UU i} {B : UU j} → A → (coprod A B) → (UU i)
  code-left a₀ (inl a) = Id a₀ a
  code-left a₀ (inr b) = Lift 𝟘

  code-right : {i j : Level} {A : UU i} {B : UU j} → B → (coprod A B) → (UU j)
  code-right b₀ (inr b) = Id b₀ b
  code-right b₀ (inl a) = Lift 𝟘

  encode-left : {i j : Level} {A : UU i} {B : UU j} → (a₀ : A) → (x : coprod A B) → (p : Id (inl a₀) x) → (code-left a₀ x)
  encode-left a₀ x p = tr (code-left a₀) p refl

  decode-left : {i j : Level} {A : UU i} {B : UU j} → (a₀ : A) → (x : coprod A B) → (c : (code-left a₀ x)) → Id (inl a₀) x
  decode-left a₀ (inl a) refl = refl
  decode-left a₀ (inr b) c    = ind-empty (Lift.raise c)

module Nats where
  code : ℕ → ℕ → (UU lzero)
  code zero-ℕ     zero-ℕ     = 𝟙
  code (succ-ℕ m) zero-ℕ     = Lift 𝟘
  code zero-ℕ     (succ-ℕ n) = Lift 𝟘
  code (succ-ℕ m) (succ-ℕ n) = code m n

  recursion : (n : ℕ) → code n n
  recursion zero-ℕ     = star
  recursion (succ-ℕ n) = recursion n

  encode : (m n : ℕ) → (Id m n) → (code m n)
  encode m n p = tr (code m) p (recursion m)

  decode : (m n : ℕ) → (code m n) → (Id m n)
  decode zero-ℕ     zero-ℕ     s = refl
  decode (succ-ℕ m) zero-ℕ     e = ind-empty (Lift.raise e)
  decode zero-ℕ     (succ-ℕ n) e = ind-empty (Lift.raise e)
  decode (succ-ℕ m) (succ-ℕ n) c = ap succ-ℕ (decode m n c)

  -- This doesn't work.
  constant-fn : (n : ℕ) → code n n
  constant-fn n = star
