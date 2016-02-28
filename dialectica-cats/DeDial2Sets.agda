-----------------------------------------------------------------------
-- This file defines Degenerate Dial₂(Sets) and shows that it is a   --
-- CCC.                                                              --
-----------------------------------------------------------------------
module DeDial2Sets where

open import prelude

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (U → Set)


-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , α) (V , β) =
  Σ[ f ∈ (U → V) ](∀{u : U} → α u → β (f u))

-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , α)} {(V , β)} {(W , γ)} (f , p₁) (g , p₂) =
  (g ∘ f , (λ {u} p-α → p₂ (p₁ p-α)))

infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , α)} = (id-set , id-set)

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safly ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , α)}{(V , β)} (f , p₁) (g , p₂) = f ≡ g


≡h-refl : {A B : Obj}{f : Hom A B} → f ≡h f
≡h-refl {U , α}{V , β}{f , _} = refl

≡h-trans : ∀{A B}{f g h : Hom A B} → f ≡h g → g ≡h h → f ≡h h
≡h-trans {U , α}{V , β}{f , _}{g , _}{h , _} p₁ p₂ rewrite p₁ | p₂ = refl


≡h-sym : ∀{A B}{f g : Hom A B} → f ≡h g → g ≡h f
≡h-sym {U , α}{V , β}{f , _}{g , _} p₁ rewrite p₁ = refl


≡h-subst-○ : ∀{A B C}{f₁ f₂ : Hom A B}{g₁ g₂ : Hom B C}{j : Hom A C}
  → f₁ ≡h f₂
  → g₁ ≡h g₂
  → f₂ ○ g₂ ≡h j
  → f₁ ○ g₁ ≡h j
≡h-subst-○ {U , α}
         {V , β}
         {W , γ}
         {f₁ , _}
         {f₂ , _}
         {g₁ , _}
         {g₂ , _}
         {j , _}
         p₅ p₆ p₇ rewrite p₅ | p₆ | p₇ = refl

○-assoc : ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
  → f ○ (g ○ h) ≡h (f ○ g) ○ h
○-assoc {U , α}{V , β}{W , γ}{S , ι}
        {f , _}{g , _}{h , _} = refl

○-idl : ∀{A B}{f : Hom A B} → id ○ f ≡h f
○-idl {U , _}{V , _}{f , _} = refl


○-idr : ∀{A B}{f : Hom A B} → f ○ id ≡h f
○-idr {U , _}{V , _}{f , _} = refl


-----------------------------------------------------------------------
-- Dial₂(Sets) is a SMC                                              --
-----------------------------------------------------------------------

-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U V : Set} → (α : U → Set) → (β : V → Set) → (U × V) → Set
_⊗ᵣ_ α β (u , v) = (α u) × (β v)

_⊗ₒ_ : (A B : Obj) → Obj
(U , α) ⊗ₒ (V , β) = ((U × V) , α ⊗ᵣ β)

_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
_⊗ₐ_ {(U , α)}{(V , β)}{(W , γ)}{(S , δ)} (f , p₁) (g , p₂) = ⟨ f , g ⟩ , cond
 where
  cond : {u : Σ U (λ x → V)} → (α ⊗ᵣ β) u → (γ ⊗ᵣ δ) (⟨ f , g ⟩ u)
  cond {u , v} (a , b) = p₁ a , p₂ b

-- The unit for tensor:
ι : ⊤ → Set
ι triv = ⊤

I : Obj
I = (⊤ , ι)

J : Obj
J = (⊤ , (λ x → ⊥))

-- The left-unitor:
λ⊗ : ∀{A : Obj} → Hom (I ⊗ₒ A) A
λ⊗ {(U , α)} = snd , cond
 where
   cond : {u : Σ ⊤ (λ x → U)} → (ι ⊗ᵣ α) u → α (snd u)
   cond {triv , u} (a , b) = b

λ⁻¹⊗ : ∀{A : Obj} → Hom A (I ⊗ₒ A)
λ⁻¹⊗ {(U , α)} = (λ u → triv , u) , cond
 where
  cond : {u : U} → α u → Σ ⊤ (λ x → α u)
  cond {u} p = triv , p

-- The right-unitor:
ρ⊗ : ∀{A : Obj} → Hom (A ⊗ₒ I) A
ρ⊗ {(U , α)} = fst , cond
 where
  cond : {u : Σ U (λ x → ⊤)} → (α ⊗ᵣ ι) u → α (fst u)
  cond {a , b} (a₁ , b₁) = a₁

ρ⊗-inv : ∀{A : Obj} → Hom A (A ⊗ₒ I)
ρ⊗-inv {(U , α)} = (λ x → x , triv) , cond 
 where
  cond : {u : U} → α u → Σ (α u) (λ x → ⊤)
  cond {u} p = p , triv

-- Symmetry:
β⊗ : ∀{A B : Obj} → Hom (A ⊗ₒ B) (B ⊗ₒ A)
β⊗ {(U , α)}{(V , β)} = twist-× , cond
 where
   cond : {u : U × V} → (α ⊗ᵣ β) u → (β ⊗ᵣ α) (twist-× u)
   cond {u , v} (a , b) = b , a


-- The associator:
α⊗-inv : ∀{A B C : Obj} → Hom (A ⊗ₒ (B ⊗ₒ C)) ((A ⊗ₒ B) ⊗ₒ C)
α⊗-inv {(U , α)}{(V , β)}{(W , γ)} = rl-assoc-× , cond
 where
   cond : {u : Σ U (λ x → Σ V (λ x₁ → W))} → (α ⊗ᵣ (β ⊗ᵣ γ)) u → ((α ⊗ᵣ β) ⊗ᵣ γ) (rl-assoc-× u)
   cond {a , a₁ , b} (a₂ , b₁ , b₂) = (a₂ , b₁) , b₂

α⊗ : ∀{A B C : Obj} → Hom ((A ⊗ₒ B) ⊗ₒ C) (A ⊗ₒ (B ⊗ₒ C)) 
α⊗ {(U , α)}{(V , β)}{(W , γ)} = (lr-assoc-× , cond)
 where
  cond : {u : Σ (Σ U (λ x → V)) (λ x → W)} → ((α ⊗ᵣ β) ⊗ᵣ γ) u → (α ⊗ᵣ (β ⊗ᵣ γ)) (lr-assoc-× u)
  cond {(a , b) , b₁} ((a₁ , b₂) , b₃) = a₁ , (b₂ , b₃)


α⊗-id₁ : ∀{A B C} → (α⊗ {A}{B}{C}) ○ α⊗-inv ≡h id
α⊗-id₁ {U , α}{V , β}{W , γ} = ext-set aux
 where
   aux : {a : Σ (Σ U (λ x → V)) (λ x → W)} → rl-assoc-× (lr-assoc-× a) ≡ a
   aux {(u , v) , w} = refl


α⊗-id₂ : ∀{A B C} → (α⊗-inv {A}{B}{C}) ○ α⊗ ≡h id
α⊗-id₂ {U , α}{V , β}{W , γ} = ext-set aux
 where
   aux : {a : Σ U (λ x → Σ V (λ x₁ → W))} → lr-assoc-× (rl-assoc-× a) ≡ a
   aux {u , (v , w)} = refl

π₁ : {A B : Obj} → Hom (A ⊗ₒ B) A
π₁ {U , α}{V , β} = fst , cond
 where
  cond : {u : Σ U (λ x → V)} → (α ⊗ᵣ β) u → α (fst u)
  cond {a , b} (a₁ , b₁) = a₁

π₂ : {A B : Obj} → Hom (A ⊗ₒ B) B
π₂ {U , α}{V , β} = snd , cond
 where
  cond : {u : Σ U (λ x → V)} → (α ⊗ᵣ β) u → β (snd u)
  cond {a , b} (a₁ , b₁) = b₁

cart-ar : {A B C : Obj}
  → (f : Hom C A)
  → (g : Hom C B)
  → Hom C (A ⊗ₒ B)
cart-ar {U , α}{V , β}{W , γ} (f , p₁) (g , p₂) = trans-× f g , cond
 where
   cond : {u : W} → γ u → Σ (α (f u)) (λ x → β (g u))
   cond {w} p = p₁ p , p₂ p

cart-diag₁ : ∀{A B C : Obj}
  → {f : Hom C A}
  → {g : Hom C B}
  → (cart-ar f g) ○ π₁ ≡h f
cart-diag₁ {U , α}{V , β}{W , γ}{f , p₁}{g , p₂} = refl


cart-diag₂ : ∀{A B C : Obj}
  → {f : Hom C A}
  → {g : Hom C B}
  → (cart-ar f g) ○ π₂ ≡h g
cart-diag₂ {U , α}{V , y}{W , γ}{f , p₁}{g , p₂} = refl


-- Internal hom:
⊸-cond : ∀{U V X Y : Set} → (U → X → Set) → (V → Y → Set) → (U → V) × (Y → X) → U × Y → Set
⊸-cond α β (f , g) (u , y) = α u (g y) → β (f u) y

_⊸ₒ_ : Obj → Obj → Obj
(U , α) ⊸ₒ (V , β) = (U → V) , (λ f → ∀{u : U} → α u → β (f u))


_⊸ₐ_ : {A B C D : Obj} → Hom C A → Hom B D → Hom (A ⊸ₒ B) (C ⊸ₒ D)
_⊸ₐ_ {(U , α)}{(V , β)}{(W , γ)}{(S , δ)} (f , p₁) (g , p₂) =
  (λ h w → g (h (f w))) , cond
  where
  cond : {h : U → V} → ({u : U} → α u → β (h u)) → {w : W} → γ w → δ (g (h (f w)))
  cond {h} p {w} p' = p₂ (p (p₁ p'))
  
cur : {A B C : Obj}
  → Hom (A ⊗ₒ B) C
  → Hom A (B ⊸ₒ C)
cur {U , α}{V , β}{W , γ} (f , p₁)
  = (λ u v → f (u , v)) , cond
 where
  cond : {u : U} → α u → {v : V} → β v → γ (f (u , v))
  cond {u} p {v} p' = p₁ (p , p')
   
cur-≡h : ∀{A B C}{f₁ f₂ : Hom (A ⊗ₒ B) C}
  → f₁ ≡h f₂
  → cur f₁ ≡h cur f₂
cur-≡h {U , α}{V , β}{W , γ}
       {f₁ , p₁}{f₂ , p₂} p₃ rewrite p₃ = refl

cur-cong : ∀{A B C}{f₁ f₂ : Hom (A ⊗ₒ B) C} → f₁ ≡h f₂ → cur f₁ ≡h cur f₂
cur-cong {(U , α)} {(V , β)} {(W , γ)}{f₁ , _}{f₂ , _} p₁ rewrite p₁ = refl


uncur : {A B C : Obj}
  → Hom A (B ⊸ₒ C)
  → Hom (A ⊗ₒ B) C
uncur {U , α}{V , β}{W , γ} (f , p₁)
  = (λ h → f (fst h) (snd h)) , cond
  where
    cond : {u : Σ U (λ x → V)} → (α ⊗ᵣ β) u → γ (f (fst u) (snd u))
    cond {a , b} (a₁ , b₁) = p₁ a₁ b₁

cur-uncur-bij₁ : ∀{A B C}{f : Hom (A ⊗ₒ B) C}
  → uncur (cur f) ≡h f
cur-uncur-bij₁ {U , α}{V , β}{W , γ}{f , p₁} = ext-set aux₁
 where
   aux₁ : {a : Σ U (λ x → V)} → f (fst a , snd a) ≡ f a
   aux₁ {u , v} = refl

cur-uncur-bij₂ : ∀{A B C}{g : Hom A (B ⊸ₒ C)}
  → cur (uncur g) ≡h g
cur-uncur-bij₂ {U , α}{V , β}{W , γ}{g , p₁} = refl
