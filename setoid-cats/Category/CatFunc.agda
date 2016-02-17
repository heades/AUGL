------------------------------------------------------------------------
-- This file contains the definition the category of functors indexed --
-- by two categories.                                                 --
------------------------------------------------------------------------
module Category.CatFunc where

open import Level

open import Category.NatTrans public

CatFunc : {l₁ l₂ : Level} → Cat {l₁} → Cat {l₂} → Cat {l₁ ⊔ l₂}
CatFunc ℂ₁ ℂ₂ = record
                  { Obj = Functor ℂ₁ ℂ₂
                  ; Hom = λ F G → record { el = NatTrans F G ; eq = λ α₁ α₂ → {!!} ; eqRpf = {!!} }
                  ; comp = {!!}
                  ; id = {!!}
                  ; assocPf = {!!}
                  ; idPfCom = {!!}
                  ; idPf = {!!}
                  }
