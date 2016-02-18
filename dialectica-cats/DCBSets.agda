module DCBSets where

open import prelude

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (Σ[ X ∈ Set ] (Σ[ m ∈ (⊤ → U) ] (Σ[ n ∈ (⊤ → X) ] (U → X → Set))))

-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , X , _ , _ , α) (V , Y , _ , _ , β) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (U → Y → X) ] (∀{u : U}{y : Y} → α u (F u y) → β (f u) y))

-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , m₁ , n₁ , α)} {(V , Y , m₂ , n₂ , β)} {(W , Z , m₃ , n₃ , γ)} (f , F  , p₁) (g , G , p₂) =
  (g ∘ f , (λ u z → F u (G (f u) z)), (λ {u} {y} p₃ → p₂ (p₁ p₃)))

infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , m , n , α)} = (id-set , curry snd , id-set)

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safely ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , X , _ , _ , α)}{(V , Y , _ , _ , β)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

≡h-refl : {A B : Obj}{f : Hom A B} → f ≡h f
≡h-refl {U , X , _ , _ , α}{V , Y , _ , _ , β}{f , F , _} = refl , refl

≡h-trans : ∀{A B}{f g h : Hom A B} → f ≡h g → g ≡h h → f ≡h h
≡h-trans {U , X , _ , _ , α}{V , Y , _ , _ , β}{f , F , _}{g , G , _}{h , H , _} (p₁ , p₂) (p₃ , p₄) rewrite p₁ | p₂ | p₃ | p₄ = refl , refl

≡h-sym : ∀{A B}{f g : Hom A B} → f ≡h g → g ≡h f
≡h-sym {U , X , _ , _ , α}{V , Y , _ , _ , β}{f , F , _}{g , G , _} (p₁ , p₂) rewrite p₁ | p₂ = refl , refl

≡h-subst-○ : ∀{A B C}{f₁ f₂ : Hom A B}{g₁ g₂ : Hom B C}{j : Hom A C}
  → f₁ ≡h f₂
  → g₁ ≡h g₂
  → f₂ ○ g₂ ≡h j
  → f₁ ○ g₁ ≡h j
≡h-subst-○ {U , X , _ , _ , α}
         {V , Y , _ , _ , β}
         {W , Z , _ , _ , γ}
         {f₁ , F₁ , _}
         {f₂ , F₂ , _}
         {g₁ , G₁ , _}
         {g₂ , G₂ , _}
         {j , J , _}
         (p₅ , p₆) (p₇ , p₈) (p₉ , p₁₀) rewrite p₅ | p₆ | p₇ | p₈ | p₉ | p₁₀ = refl , refl

○-assoc : ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
  → f ○ (g ○ h) ≡h (f ○ g) ○ h
○-assoc {U , X , _ , _ , α}{V , Y , _ , _ , β}{W , Z , _ , _ , γ}{S , T , _ , _ , ι}
        {f , F , _}{g , G , _}{h , H , _} = refl , refl

○-idl : ∀{A B}{f : Hom A B} → id ○ f ≡h f
○-idl {U , X , _ , _ , _}{V , Y , _ , _ , _}{f , F , _} = refl , refl

○-idr : ∀{A B}{f : Hom A B} → f ○ id ≡h f
○-idr {U , X , _ , _ , _}{V , Y , _ , _ , _}{f , F , _} = refl , refl

-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U X V Y : Set} → (U → X → Set) → (V → Y → Set) → ((U × V) → (X × Y) → Set)
_⊗ᵣ_ α β (u , v) (x , y) = (α u x) × (β v y)

_⊗ₒ_ : (A B : Obj) → Obj
(U , X , m₁ , n₁ , α) ⊗ₒ (V , Y , m₂ , n₂ , β) = ((U × V) , (X × Y) , trans-× m₁ m₂  , trans-× n₁ n₂ , α ⊗ᵣ β)

F⊗ : ∀{Z T V X U Y : Set}{F : U → Z → X}{G : V → T → Y} → (U × V) → (Z × T) → (X × Y)
F⊗ {F = F}{G} (u , v) (z , t) = F u z , G v t
  
_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
_⊗ₐ_ {(U , X , _ , _ , α)}{(V , Y , _ , _ , β)}{(W , Z , _ , _ , γ)}{(S , T , _ , _ , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {F = F}{G} , p⊗
 where
  p⊗ : {u : Σ U (λ x → V)} {y : Σ Z (λ x → T)} → (α ⊗ᵣ β) u (F⊗ {F = F}{G} u y) → (γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y
  p⊗ {u , v}{z , t} (p₃ , p₄) = p₁  p₃ , p₂ p₄

π₁ : {U X V Y : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {m₁ : ⊤ → U}
    → {n₁ : ⊤ → X}
    → {m₂ : ⊤ → V}
    → {n₂ : ⊤ → Y}    
    → Hom ((U , X , m₁ , n₁ , α) ⊗ₒ (V , Y , m₂ , n₂ , β)) (U , X , m₁ , n₁ , α)
π₁ {U}{X}{V}{Y}{α}{β}{m₁}{n₁}{m₂}{n₂} = fst , (λ r x → x , n₂ triv) , cond
 where
   cond : {u : Σ U (λ x → V)} {y : X} → (α ⊗ᵣ β) u (y , n₂ triv) → α (fst u) y
   cond {u , v}{x} (p₁ , p₂) = p₁

π₂ : {U X V Y : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {m₁ : ⊤ → U}
    → {n₁ : ⊤ → X}
    → {m₂ : ⊤ → V}
    → {n₂ : ⊤ → Y}    
    → Hom ((U , X , m₁ , n₁ , α) ⊗ₒ (V , Y , m₂ , n₂ , β)) (V , Y , m₂ , n₂ , β)
π₂ {U}{X}{V}{Y}{α}{β}{m₁}{n₁}{m₂}{n₂} = snd , (λ r y → n₁ triv , y) , cond
 where
  cond : {u : Σ U (λ x → V)} {y : Y} → (α ⊗ᵣ β) u (n₁ triv , y) → β (snd u) y
  cond {u , v}{y} (p₁ , p₂) = p₂

cart-ar : {U X V Y W Z : Set}
  → {α : U → X → Set}
  → {β : V → Y → Set}
  → {γ : W → Z → Set}
  → {m₁ : ⊤ → U}
  → {n₁ : ⊤ → X}
  → {m₂ : ⊤ → V}
  → {n₂ : ⊤ → Y}
  → {m₃ : ⊤ → W}
  → {n₃ : ⊤ → Z}      
  → Hom (W , Z , m₃ , n₃ , γ) (U , X , m₁ , n₁ , α)
  → Hom (W , Z , m₃ , n₃ , γ) (V , Y , m₂ , n₂ , β)
  → Hom (W , Z , m₃ , n₃ , γ) ((U , X , m₁ , n₁ , α) ⊗ₒ (V , Y , m₂ , n₂ , β))
cart-ar {U}{X}{V}{Y}{W}{Z}{α}{β}{γ}{m₁}{n₁}{m₂}{n₂}{m₃}{n₃} (f , F) (g , G) = trans-× f g , {!!} , {!!}
