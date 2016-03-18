module unit where

open import level
open import eq

data ⊤ {ℓ : Level} : Set ℓ where
  triv : ⊤

{-# COMPILED_DATA ⊤ () ()  #-}

single-range : ∀{ℓ}{U : Set ℓ}{g : U → ⊤ {ℓ}} → ∀{u : U} → g u ≡ triv
single-range {_}{U}{g}{u} with g u
... | triv = refl
