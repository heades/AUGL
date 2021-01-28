module sum-thms where

open import eq
open import sum
open import list
open import product
open import empty
open import negation

inj₁-inj : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}{x : A}{x'} → inj₁{ℓ}{ℓ'}{A}{B} x ≡ inj₁ x' → x ≡ x'
inj₁-inj refl = refl

⊎-assoc-iso₁ : ∀{ℓ}{U V W : Set ℓ}{x : U ⊎ V ⊎ W} → ⊎-assoc-inv (⊎-assoc x) ≡ x
⊎-assoc-iso₁ {x = inj₁ x} = refl
⊎-assoc-iso₁ {x = inj₂ (inj₁ x)} = refl
⊎-assoc-iso₁ {x = inj₂ (inj₂ y)} = refl

⊎-assoc-iso₂ : ∀{ℓ}{U V W : Set ℓ}{x : (U ⊎ V) ⊎ W} → ⊎-assoc (⊎-assoc-inv x) ≡ x
⊎-assoc-iso₂ {x = inj₁ (inj₁ x)} = refl
⊎-assoc-iso₂ {x = inj₁ (inj₂ y)} = refl
⊎-assoc-iso₂ {x = inj₂ y} = refl

⊎-left-ident-iso₁ : ∀{ℓ}{X : Set ℓ}{x} → ⊎-left-ident-inv {_}{X} (⊎-left-ident x) ≡ x
⊎-left-ident-iso₁ {x = inj₁ x} = ⊥-elim x
⊎-left-ident-iso₁ {x = inj₂ y} = refl

⊎-left-ident-iso₂ : ∀{ℓ}{X : Set ℓ}{x} → ⊎-left-ident {_}{X} (⊎-left-ident-inv x) ≡ x
⊎-left-ident-iso₂ = refl

⊎-right-ident-iso₁ : ∀{ℓ}{X : Set ℓ}{x} → ⊎-right-ident-inv {_}{X} (⊎-right-ident x) ≡ x
⊎-right-ident-iso₁ {x = inj₁ x} = refl
⊎-right-ident-iso₁ {x = inj₂ y} = ⊥-elim y

⊎-right-ident-iso₂ : ∀{ℓ}{X : Set ℓ}{x} → ⊎-right-ident {_}{X} (⊎-right-ident-inv x) ≡ x
⊎-right-ident-iso₂ = refl

¬⊎→× : ∀{ℓ}{A B : Set ℓ} → ¬ (_⊎_ {ℓ} A B) → ¬ A × ¬ B
¬⊎→× {ℓ}{A}{B} p = (λ x → p (inj₁ x)) , λ x → p (inj₂ x)
