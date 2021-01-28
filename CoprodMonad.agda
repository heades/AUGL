module CoprodMonad where

open import functor
open import monad

data PlusT (t₁ t₂ : Set → Set) (a : Set) (p₁ : Triple t₁)(p₂ : Triple t₂) : Set where
  T₁ : (t₁ (PlusT t₁ t₂ a p₁ p₂)) → PlusT t₁ t₂ a p₁ p₂
  
