module powerset where

open import level
open import list
open import bool
open import product
open import empty
open import unit
open import sum
open import eq
open import functions renaming (id to id-set) public

-- Extensionality will be used when proving equivalences of morphisms.
postulate ext-set : ∀{l1 l2 : level} → extensionality {l1} {l2}
-- These are isomorphisms, but Agda has no way to prove these as
-- equivalences.  They are consistent to adopt as equivalences by
-- univalence:
postulate ⊎-unit-r : ∀{X : Set} → (X ⊎ ⊥) ≡ X
postulate ⊎-unit-l : ∀{X : Set} → (⊥ ⊎ X) ≡ X
postulate ∧-unit : ∀{ℓ}{A : Set ℓ} → A ≡ ((⊤ {ℓ}) ∧ A)
postulate ∧-sym : ∀{ℓ}{A B : Set ℓ} → (A ∧ B) ≡ (B ∧ A)
postulate ∧-unit-r : ∀{ℓ}{A : Set ℓ} → A ≡ (A ∧ (⊤ {ℓ}))
postulate ∧-assoc : ∀{ℓ}{A B C : Set ℓ} →  (A ∧ (B ∧ C)) ≡ ((A ∧ B) ∧ C)

ℙ : {X : Set} → (X → 𝔹) → Set
ℙ {X} S = (X → 𝔹) → 𝔹

_∪_ : {X : Set}{S : X → 𝔹} → ℙ S → ℙ S → ℙ S
(s₁ ∪ s₂) x = (s₁ x) || (s₂ x)

_∩_ : {X : Set}{S : X → 𝔹} → ℙ S → ℙ S → ℙ S
(s₁ ∩ s₂) x = (s₁ x) && (s₂ x)

_×S_ : {X Y : Set} → (S₁ : X → 𝔹) → (S₂ : Y → 𝔹) →  (X × Y) → 𝔹
_×S_ S₁ S₂ (a , b) = (S₁ a) && (S₂ b)

π₁ : ∀{X Y : Set} → ((Σ X (λ x → Y) → 𝔹) → 𝔹) → ((X → 𝔹) → 𝔹)
π₁ P S = P (λ x → S (fst x))
   
π₂ : ∀{X Y : Set} → ((Σ X (λ x → Y) → 𝔹) → 𝔹) → ((Y → 𝔹) → 𝔹)
π₂ P S = P (λ x → S (snd x))

i₁ : {X Y : Set}{S₁ : X → 𝔹}{S₂ : Y → 𝔹} → ℙ S₁ → (((X × Y) → 𝔹) → 𝔹)
i₁ {X}{Y}{S₁}{S₂} P S = {!!}

i₂ : {X Y : Set}{S₁ : X → 𝔹}{S₂ : Y → 𝔹} → ℙ S₂ → ℙ (S₁ ×S S₂)
i₂ {X}{Y}{S₁}{S₂} P _ = P S₂

cp-ar : {X Y Z : Set}{S₁ : X → 𝔹}{S₂ : Y → 𝔹}{S₃ : Z → 𝔹} → (ℙ S₁ → ℙ S₃) → (ℙ S₂ → ℙ S₃) → ℙ (S₁ ×S S₂) → ℙ S₃
cp-ar {X}{Y}{Z}{S₁}{S₂}{S₃} f g P S = (f (π₁ P) S) || (g (π₂ P) S)

cp-diag₁ : {X Y Z : Set}{S₁ : X → 𝔹}{S₂ : Y → 𝔹}{S₃ : Z → 𝔹}{f : ℙ S₁ → ℙ S₃}{g : ℙ S₂ → ℙ S₃} → cp-ar {X}{Y}{Z}{S₁}{S₂}{S₃ = S₃} f g ∘ (i₁ {X}{Y}{S₁}{S₂}) ≡ f
cp-diag₁ {X}{Y}{Z}{S₁}{S₂}{S₃}{f}{g} = ext-set (λ {x} → ext-set (λ {S} → {!!}))

-- cp-diag₂ : {X Y Z : Set}{f : Z → X}{g : Z → Y} → cp-ar f g ∘ i₂ ≡ ℙₐ g
-- cp-diag₂ {X}{Y}{Z}{f}{g} = refl

-- co-curry : {A B C : Set} → ((A × B) → C) → ℙ (B → C) → ℙ A
-- co-curry {A}{B}{C} f = ℙₐ {A}{B → C} (curry f)

-- co-uncurry : {A B C : Set} → (A → B → C) → ℙ C → ℙ (A × B)
-- co-uncurry {A}{B}{C} f = ℙₐ {A × B} {C} (uncurry f)

-- liftℙ : {A B : Set} → (A → ℙ B) → ℙ A → ℙ B
-- liftℙ {A} f s b = ∀(a : A) → (s a) × (f a b)
