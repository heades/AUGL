module neq where

open import eq
open import negation

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infix 4 _≢_ 

----------------------------------------------------------------------
-- defined types
----------------------------------------------------------------------

_≢_ : ∀ {ℓ}{A : Set ℓ} → A → A → Set ℓ
x ≢ y = ¬ (x ≡ y)

sym-≢ : ∀{ℓ}{A : Set ℓ}{x y : A} → x ≢ y → y ≢ x 
sym-≢ p₁ p₂ = p₁ (sym p₂)
