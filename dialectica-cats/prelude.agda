module prelude where

open import level public
open import product public
open import product-thms public
open import sum public
open import empty public
open import unit public
open import functions renaming (id to id-set) public
open import eq public
open import list public
open import list-thms public
open import bool public
open import nat public
open import nat-thms public

-- Extensionality will be used when proving equivalences of morphisms.
postulate ext-set : ∀{l1 l2 : level} → extensionality {l1} {l2}
-- These are isomorphisms, but Agda has no way to prove these as
-- equivalences.  They are consistent to adopt as equivalences by
-- univalence:
postulate ∧-unit : ∀{ℓ}{A : Set ℓ} → A ≡ (⊤ ∧ A)
postulate ∧-assoc : ∀{ℓ}{A B C : Set ℓ} →  (A ∧ (B ∧ C)) ≡ ((A ∧ B) ∧ C)
postulate ∧-twist : ∀{ℓ}{A B : Set ℓ} →  (A ∧ B) ≡ (B ∧ A)
-- Provable from the above axioms:
postulate assoc-twist₁ : {A B C D : Set} → ((A × C) × (B × D)) ≡ ((A × B) × (C × D))

-- The following defines a commutative monoid as lists:
_* = 𝕃

postulate *-comm : ∀{A : Set}{l₁ l₂ : A *} → l₁ ++ l₂ ≡ l₂ ++ l₁

×-⊥₁ : (⊥ × ⊥) → ⊥
×-⊥₁ (x , y) = x

tar⊥-× : {A B : Set}
  → (f : A -> ⊥)
  → (g : B → ⊥)
  → (A × B) → ⊥
tar⊥-× f g (a , b) = ×-⊥₁ ((f a , g b))       

