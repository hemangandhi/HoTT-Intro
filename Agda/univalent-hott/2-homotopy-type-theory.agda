{-# OPTIONS --without-K --exact-split #-}

import 05-identity-types
open 05-identity-types public

-- Inversion is uninteresting and comes from:
inversion-proof :
  {i : Level} {A : UU i} (x y : A) → Id x y → Id y x
inversion-proof x y = ind-Id x (λ y' p' → Id y' x) (refl x) y
