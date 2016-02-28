-----------------------------------------------------------------------
-- This file defines Degenerate Dial₂(Sets) and shows that it is a   --
-- CCC.                                                              --
-----------------------------------------------------------------------
module DeDial2Sets where

open import prelude
open import Dial2Sets

Obj⊤ : Set₁
Obj⊤ = Σ[ U ∈ Set ] (U → Set)

toObj-cond : {U : Set} → (α : U → Set) → U → ⊤ → Set
toObj-cond {U} α u triv = α u 

toObj : Obj⊤ → Obj
toObj (U , α) = U , ⊤ , toObj-cond α

π₁ : {A B : Obj⊤} → Hom ((toObj A) ⊗ₒ (toObj B)) (toObj A)
π₁ {U , α}{V , β} = fst , ctr , cond
 where
  ctr : ⊤ → Σ (V → ⊤) (λ x → U → ⊤)
  ctr triv = (λ _ → triv) , (λ _ → triv)

  cond : {u : Σ U (λ x → V)} {y : ⊤} → (toObj-cond α ⊗ᵣ toObj-cond β) u (ctr y) → toObj-cond α (fst u) y
  cond {a , b} {triv} (a₁ , b₁) = a₁

π₂ : {A B : Obj⊤} → Hom ((toObj A) ⊗ₒ (toObj B)) (toObj B)
π₂ {U , α}{V , β} = snd , ctr , cond
 where
  ctr : ⊤ → Σ (V → ⊤) (λ x → U → ⊤)
  ctr triv = (λ _ → triv) , (λ _ → triv)

  cond : {u : Σ U (λ x → V)} {y : ⊤} → (toObj-cond α ⊗ᵣ toObj-cond β) u (ctr y) → toObj-cond β (snd u) y
  cond {a , b} {triv} (a₁ , b₁) = b₁

cart-ar : {A B C : Obj⊤}
  → (f : Hom (toObj C) (toObj A))
  → (g : Hom (toObj C) (toObj B))
  → Hom (toObj C) ((toObj A) ⊗ₒ (toObj B))
cart-ar {U , α}{V , β}{W , γ} (f , F , p₁) (g , G , p₂) = trans-× f g ,  ctr , cond
 where
  ctr : Σ (V → ⊤) (λ x → U → ⊤) → ⊤
  ctr _ = triv

  cond : {u : W} {y : Σ (V → ⊤) (λ x → U → ⊤)} → γ u → (toObj-cond α ⊗ᵣ toObj-cond β) (f u , g u) y
  cond {w}{y = a , b} x with p₁ {w}{triv} | p₂ {w}{triv}
  ... | p' | p'' with F triv | G triv
  ... | triv | triv with a (g w) | b (f w)
  ... | triv | triv = p' x , p'' x

cart-diag₁ : ∀{A B C : Obj⊤}
  → {f : Hom (toObj C) (toObj A)}
  → {g : Hom (toObj C) (toObj B)}
  → (cart-ar f g) ○ π₁ ≡h f
cart-diag₁ {U , α}{V , β}{W , γ}{f , F , p₁}{g , G , p₂} = refl , ext-set ctr
 where
   ctr : {a : ⊤} → triv ≡ F a
   ctr {triv} with F triv
   ... | triv = refl

cart-diag₂ : ∀{A B C : Obj⊤}
  → {f : Hom (toObj C) (toObj A)}
  → {g : Hom (toObj C) (toObj B)}
  → (cart-ar f g) ○ π₂ ≡h g
cart-diag₂ {U , α}{V , β}{W , γ}{f , F , p₁}{g , G , p₂} = refl , ext-set ctr
 where
   ctr : {a : ⊤} → triv ≡ G a
   ctr {triv} with G triv
   ... | triv = refl
   
□ₒ : Obj → Obj
□ₒ A = !ₒ A

□ₐ : {A B : Obj⊤} → Hom (toObj A) (toObj B) → Hom (□ₒ (toObj A)) (□ₒ (toObj B))
□ₐ m = !ₐ m

ε-□ : ∀{A} → Hom (□ₒ (toObj A)) (toObj A)
ε-□ = ε

δ-□ : ∀{A} → Hom (□ₒ (toObj A)) (□ₒ (□ₒ (toObj A)))
δ-□ = δ
