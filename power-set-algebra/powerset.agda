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

ℙ : Set → Set₁
ℙ X = X → Set

ℙₐ : {X Y : Set} → (X → Y) → ℙ Y → ℙ X
ℙₐ f s x = s (f x)

_∪_ : {X : Set} → ℙ X → ℙ X → ℙ X
(s₁ ∪ s₂) x = (s₁ x) ⊎ (s₂ x)

_∩_ : {X : Set} → ℙ X → ℙ X → ℙ X
(s₁ ∩ s₂) x = (s₁ x) × (s₂ x)

¬_ : {X : Set} → ℙ X → ℙ X
(¬ s₁) x = (s₁ x) → ⊥

∅ : {X : Set} → ℙ X
∅ _ = ⊥

carrier : {X : Set} → ℙ X
carrier _ = ⊤

∪-unit₁ : ∀{X : Set}{s : ℙ X} → s ∪ ∅ ≡ s
∪-unit₁ {X}{s} = ext-set aux
 where
  aux : {a : X} → (s a ⊎ ⊥) ≡ s a
  aux {x} = ⊎-unit-r {s x}

∪-unit₂ : ∀{X : Set}{s : ℙ X} → ∅ ∪ s ≡ s
∪-unit₂ {X}{s} = ext-set aux
 where
   aux : {a : X} → (⊥ ⊎ s a) ≡ s a
   aux {x} = ⊎-unit-l

∩-unit₁ : ∀{X : Set}{s : ℙ X} → s ∩ carrier ≡ s
∩-unit₁ {X}{s} = ext-set aux
 where
   aux : {a : X} → Σ (s a) (λ x → ⊤) ≡ s a
   aux {x} = sym (∧-unit-r {_}{s x})

∩-unit₂ : ∀{X : Set}{s : ℙ X} → carrier ∩ s ≡ s
∩-unit₂ {X}{s} = ext-set aux
 where
   aux : {a : X} → Σ ⊤ (λ x → s a) ≡ s a
   aux {x} = sym (∧-unit {_}{s x})

i₁ : {X Y : Set} → ℙ X → ℙ (X × Y)
i₁ = ℙₐ fst

i₂ : {X Y : Set} → ℙ Y → ℙ (X × Y)
i₂ = ℙₐ snd

cp-ar : {X Y Z : Set} → (Z → X) → (Z → Y) → ℙ (X × Y) → ℙ Z
cp-ar f g = ℙₐ (trans-× f g)

cp-diag₁ : {X Y Z : Set}{f : Z → X}{g : Z → Y} → cp-ar f g ∘ i₁ ≡ ℙₐ f
cp-diag₁ {X}{Y}{Z}{f}{g} = refl

cp-diag₂ : {X Y Z : Set}{f : Z → X}{g : Z → Y} → cp-ar f g ∘ i₂ ≡ ℙₐ g
cp-diag₂ {X}{Y}{Z}{f}{g} = refl

co-curry : {A B C : Set} → ((A × B) → C) → ℙ (B → C) → ℙ A
co-curry {A}{B}{C} f = ℙₐ {A}{B → C} (curry f)

co-uncurry : {A B C : Set} → (A → B → C) → ℙ C → ℙ (A × B)
co-uncurry {A}{B}{C} f = ℙₐ {A × B} {C} (uncurry f)

liftℙ : {A B : Set} → (A → ℙ B) → ℙ A → ℙ B
liftℙ {A} f s b = ∀(a : A) → (s a) × (f a b)
