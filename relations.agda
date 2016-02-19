{- This file describes properties of computable relations. -}

open import bool
open import level
open import eq
open import product
open import product-thms
open import negation

module relations where

  -- Decidable relations.
  -- This was taken from the Agda STDLIB.
  data Dec {p} (P : Set p) : Set p where
    yes : ( p :   P) → Dec P
    no  : (¬p : ¬ P) → Dec P
  
  module relationsOld {ℓ ℓ' : level}{A : Set ℓ} (_≥A_ : A → A → Set ℓ') where

    reflexive : Set (ℓ ⊔ ℓ')
    reflexive = ∀ {a : A} → a ≥A a 

    transitive : Set (ℓ ⊔ ℓ')
    transitive = ∀ {a b c : A} → a ≥A b → b ≥A c → a ≥A c

    preorder : Set (ℓ ⊔ ℓ')
    preorder = reflexive ∧ transitive

    _iso_ : A → A → Set ℓ'
    d iso d' = d ≥A d' ∧ d' ≥A d

    iso-intro : ∀{x y : A} → x ≥A y → y ≥A x → x iso y 
    iso-intro p1 p2 = p1 , p2
  

