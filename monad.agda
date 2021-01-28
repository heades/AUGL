module monad where

open import eq

open import functor
open import functions

record Triple (T : Set → Set) : Set₁ where
  constructor MkTriple
  field
    η : ∀{A : Set} → A → T A
    μ : ∀{A : Set} → T (T A) → T A
    η-inv : ∀{A : Set} → T A → A

    -- triple-func : Functor T
    -- triple-assoc : ∀{A : Set} → μ {A} ∘ (fmap triple-func μ) ≡ (μ ∘ μ)
    -- triple-id₁ : ∀{A : Set} → μ ∘ η {T A} ≡ id
    -- triple-id₂ : ∀{A : Set} → (μ {A} ∘ fmap triple-func (η {A})) ≡ id

record Monad (M : Set → Set) : Set₁ where
  constructor MkMonad
  field  
    return : ∀{A : Set} → A → M A
    bind : ∀{A B : Set} → M A → (A → M B) → M B

    -- monad-funct : Functor M

    -- monad-left-id : ∀{A B : Set}{a : A}{f : A → M B}
    --   → bind (return a) f ≡ f a
      
    -- monad-right-id : ∀{A : Set}{c : M A}
    --   → bind c return ≡ c
      
    -- monad-assoc : ∀{A B C : Set}{c : M A}{f : A → M B}{g : B → M C}
    --   → bind (bind c f) g ≡ bind c (λ a → bind (f a) g)
