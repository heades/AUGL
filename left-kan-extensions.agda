module left-kan-extensions where

open import functor

-- The left-kan extension of G along J.
record left-kan (G : Set → Set) (J : Set → Set) (pG : Functor G) (pJ : Functor J) : Set₁ where
  field
    lan : Set → Set
    pLan : Functor lan

    
