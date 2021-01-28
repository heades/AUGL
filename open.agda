module Open where

open import bool
open import nat
open import product
open import sum
open import functor

data Row : Set₁ where
  Empty : Row
  Ty : Set → Row  
  Prod : Row → Row → Row

infixr 19 _♯_ 

_′ = Ty
_♯_ = Prod 

all : Row → Set
all Empty = ⊤
all (Ty x) = x
all (Prod r₁ r₂) = (all r₁) × (all r₂)

one : Row → Set
one Empty = ⊥
one (Ty x) = x
one (Prod r₁ r₂) = (one r₁) ⊎ (one r₂)

_⊗_ : {A B : Row} → all A → all B → all (A ♯ B)
_⊗_ p₁ p₂ = p₁ , p₂

_&_ : {A : Set}{B : Row} → A → all B → all (A ′ ♯ B)
_&_ {A}{B} = _⊗_ {A ′}{B}

_⊕_ : {A B : Row} → (one A) ⊎ (one B) → one (A ♯ B)
_⊕_ p = p

⊕inj₁ : {A B : Row} → one A → one (A ♯ B)
⊕inj₁ = inj₁
⊕inj₂ : {A B : Row} → one B → one (A ♯ B)
⊕inj₂ = inj₂

inj : {A : Set}{B : Row} → A → one (A ′ ♯ B)
inj {A}{B} = ⊕inj₁ {A ′}{B}

test₁ : all (ℕ ′ ♯ 𝔹 ′ ♯ Empty)
test₁ = _&_ {ℕ}{𝔹 ′ ♯ Empty} 1 (_&_ {𝔹}{Empty} tt triv)
