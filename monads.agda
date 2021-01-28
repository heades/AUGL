module monad where

open import eq

record Monad (M : Set → Set) : Set₁ where
  field
    return : ∀{A : Set} → A → M A
    bind : ∀{A B : Set} → M A → (A → M B) → M B
    
    monad-left-id : ∀{A B : Set}{a : A}{f : A → M B}
      → bind (return a) f ≡ f a
      
    monad-right-id : ∀{A : Set}{c : M A}
      → bind c return ≡ c
      
    monad-assoc : ∀{A B C : Set}{c : M A}{f : A → M B}{g : B → M C}
      → bind (bind c f) g ≡ bind c (λ a → bind (f a) g)

