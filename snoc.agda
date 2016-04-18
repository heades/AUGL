module snoc where

open import unit
open import empty
open import bool
open import product

data Snoc (A : Set) : Set where
  [] : Snoc A
  _::_ : Snoc A → A → Snoc A

infixl 6 _::_ _++_

[_] : {A : Set} → A → Snoc A
[ x ] = [] :: x

_++_ : {A : Set} → Snoc A → Snoc A → Snoc A
[] ++ l₂ = l₂
(l₁ :: x) ++ l₂ = (l₁ ++ l₂) :: x

member : {A : Set} → (A → A → 𝔹) → A → Snoc A → 𝔹
member _=A_ x (l :: y) with x =A y
... | tt = tt
... | ff = ff
member _=A_ x _ = ff

inPairSnocFst : {A B : Set} → (A → A → 𝔹) → A → Snoc (A × B) → Set
inPairSnocFst _=A_ x [] = ⊥
inPairSnocFst _=A_ x (l :: (a , _)) with x =A a
... | tt = ⊤
... | ff = inPairSnocFst _=A_ x l
