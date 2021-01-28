module empty where

open import level

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data ⊥ {ℓ : Level} : Set ℓ where

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

----------------------------------------------------------------------
-- theorems
----------------------------------------------------------------------
⊥-elim : ∀{ℓ} → ⊥ {ℓ} → ∀{ℓ'}{P : Set ℓ'} → P
⊥-elim ()

