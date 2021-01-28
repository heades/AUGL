module functor where

open import level

record Functor {ℓ : Level} (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  constructor mkFunc
  field
    fmap : ∀{A B : Set ℓ} → (A → B) → F A → F B

open Functor public
