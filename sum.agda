module sum where

open import level
open import bool
open import eq
open import maybe
open import product
open import empty

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data _⊎_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

_∨_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
_∨_ = _⊎_

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixr 1 _⊎_ _∨_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

_≫=⊎_ : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}{C : Set (ℓ ⊔ ℓ')}  → A ⊎ B → (B → A ⊎ C) → A ⊎ C
inj₁ x ≫=⊎ f = inj₁ x
inj₂ x ≫=⊎ f = f x

return⊎ : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → B → A ⊎ B
return⊎ b = inj₂ b

infix 5 error⊎_

error⊎_ : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → A → A ⊎ B
error⊎_ a = inj₁ a

extract-inj₁≡ : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'}{a a' : A} → inj₁{B = B} a ≡ inj₁ a' → a ≡ a'
extract-inj₁≡ refl = refl

extract-inj₂≡ : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'}{b b' : B} → inj₂{A = A} b ≡ inj₂ b' → b ≡ b'
extract-inj₂≡ refl = refl

=⊎ : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'} → (A → A → 𝔹) → (B → B → 𝔹) → A ⊎ B → A ⊎ B → 𝔹
=⊎ eqa eqb (inj₁ a) (inj₁ a') = eqa a a'
=⊎ eqa eqb (inj₂ b) (inj₂ b') = eqb b b'
=⊎ _ _ _ _ = ff


=⊎-to-≡ : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'} → (_eqa_ : A → A → 𝔹) → (_eqb_ : B → B → 𝔹) → ((a a' : A) → (a eqa a' ≡ tt) → a ≡ a') → ((b b' : B) → (b eqb b' ≡ tt) → b ≡ b') →  (x y : A ⊎ B) → =⊎ _eqa_ _eqb_ x y  ≡ tt → x ≡ y 
=⊎-to-≡ eqa eqb risea riseb (inj₁ a) (inj₁ a') p rewrite risea a a' p = refl
=⊎-to-≡ eqa eqb risea riseb (inj₂ b) (inj₂ b') p rewrite riseb b b' p = refl
=⊎-to-≡ eqa eqb risea riseb (inj₁ a) (inj₂ b) ()
=⊎-to-≡ eqa eqb risea riseb (inj₂ b) (inj₁ a) ()




≡⊎-to-= : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'} → (_eqa_ : A → A → 𝔹) → (_eqb_ : B → B → 𝔹) → ((a a' : A) → a ≡ a' → a eqa a' ≡ tt) → ((b b' : B) → b ≡ b' → b eqb b' ≡ tt) →  (x y : A ⊎ B) → x ≡ y → =⊎ _eqa_ _eqb_ x y  ≡ tt
≡⊎-to-= eqa eqb dropa dropb (inj₁ a) (inj₁ a') p = dropa a a' (extract-inj₁≡ p)
≡⊎-to-= eqa eqb dropa dropb (inj₂ b) (inj₂ b') p = dropb b b' (extract-inj₂≡ p)
≡⊎-to-= eqa eqb dropa dropb (inj₁ a) (inj₂ b) ()
≡⊎-to-= eqa eqb dropa dropb (inj₂ b) (inj₁ a) ()

⊎-assoc : ∀{ℓ}{U V W : Set ℓ} → U ⊎ V ⊎ W → (U ⊎ V) ⊎ W
⊎-assoc (inj₁ x) = inj₁ (inj₁ x)
⊎-assoc (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
⊎-assoc (inj₂ (inj₂ y)) = inj₂ y

⊎-assoc-inv : ∀{ℓ}{U V W : Set ℓ} → (U ⊎ V) ⊎ W → U ⊎ V ⊎ W
⊎-assoc-inv (inj₁ (inj₁ x)) = inj₁ x
⊎-assoc-inv (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
⊎-assoc-inv (inj₂ y) = inj₂ (inj₂ y)

⊎-ar : ∀{ℓ}{U V W : Set ℓ} → (U → W) → (V → W) → U ⊎ V → W
⊎-ar f g (inj₁ x) = f x
⊎-ar f g (inj₂ y) = g y

⊎-sym : ∀{ℓ}{X Y : Set ℓ} → X ⊎ Y → Y ⊎ X
⊎-sym (inj₁ x) = inj₂ x
⊎-sym (inj₂ y) = inj₁ y

⊎-left-ident : ∀{ℓ}{X : Set ℓ} → ⊥ {ℓ} ⊎ X → X
⊎-left-ident (inj₁ x) = ⊥-elim x
⊎-left-ident (inj₂ y) = y

⊎-left-ident-inv : ∀{ℓ}{X : Set ℓ} → X → ⊥ {ℓ} ⊎ X 
⊎-left-ident-inv = inj₂

⊎-right-ident : ∀{ℓ}{X : Set ℓ} → X ⊎ ⊥ {ℓ} → X
⊎-right-ident (inj₁ x) = x
⊎-right-ident (inj₂ y) = ⊥-elim y

⊎-right-ident-inv : ∀{ℓ}{X : Set ℓ} → X → X ⊎ ⊥ {ℓ} 
⊎-right-ident-inv = inj₁
