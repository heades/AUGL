module DCBSets where

open import prelude
open import relations

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (Σ[ X ∈ Set ] (Σ[ n ∈ (⊤ → X) ] (Σ[ α ∈ (U → X → Set) ]( ∀(u : U)(x : X) → Dec (α u x) ))))

-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , X , _ , α , _) (V , Y , _ , β , _) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (U → Y → X) ] (∀{u : U}{y : Y} → α u (F u y) → β (f u) y))



-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , n₁ , α , _)} {(V , Y , n₂ , β , _)} {(W , Z , n₃ , γ , _)} (f , F  , p₁) (g , G , p₂) =
  (g ∘ f , (λ u z → F u (G (f u) z)), (λ {u} {y} p₃ → p₂ (p₁ p₃)))

infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , n , α , _)} = (id-set , curry snd , id-set)

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safely ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , X , _ , α , _)}{(V , Y , _ , β , _)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

≡h-refl : {A B : Obj}{f : Hom A B} → f ≡h f
≡h-refl {U , X , _ , α , _}{V , Y , _ , β , _}{f , F , _} = refl , refl

≡h-trans : ∀{A B}{f g h : Hom A B} → f ≡h g → g ≡h h → f ≡h h
≡h-trans {U , X , _ , α , _}{V , Y , _ , β , _}{f , F , _}{g , G , _}{h , H , _} (p₁ , p₂) (p₃ , p₄) rewrite p₁ | p₂ | p₃ | p₄ = refl , refl

≡h-sym : ∀{A B}{f g : Hom A B} → f ≡h g → g ≡h f
≡h-sym {U , X , _ , α , _}{V , Y , _ , β , _}{f , F , _}{g , G , _} (p₁ , p₂) rewrite p₁ | p₂ = refl , refl

≡h-subst-○ : ∀{A B C}{f₁ f₂ : Hom A B}{g₁ g₂ : Hom B C}{j : Hom A C}
  → f₁ ≡h f₂
  → g₁ ≡h g₂
  → f₂ ○ g₂ ≡h j
  → f₁ ○ g₁ ≡h j
≡h-subst-○ {U , X , _ , α , _}
         {V , Y , _ , β , _}
         {W , Z , _ , γ , _}
         {f₁ , F₁ , _}
         {f₂ , F₂ , _}
         {g₁ , G₁ , _}
         {g₂ , G₂ , _}
         {j , J , _}
         (p₅ , p₆) (p₇ , p₈) (p₉ , p₁₀) rewrite p₅ | p₆ | p₇ | p₈ | p₉ | p₁₀ = refl , refl

○-assoc : ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
  → f ○ (g ○ h) ≡h (f ○ g) ○ h
○-assoc {U , X , _ , α , _}{V , Y , _ , β , _}{W , Z , _ , γ , _}{S , T , _ , ι , _}
        {f , F , _}{g , G , _}{h , H , _} = refl , refl

○-idl : ∀{A B}{f : Hom A B} → id ○ f ≡h f
○-idl {U , X , _ , _ , _}{V , Y , _ , _ , _}{f , F , _} = refl , refl

○-idr : ∀{A B}{f : Hom A B} → f ○ id ≡h f
○-idr {U , X , _ , _ , _}{V , Y , _ , _ , _}{f , F , _} = refl , refl

-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U X V Y : Set} → (U → X → Set) → (V → Y → Set) → ((U × V) → (X × Y) → Set)
_⊗ᵣ_ α β (u , v) (x , y) = (α u x) × (β v y)

⊗d : ∀{U V X Y}{α : U → X → Set}{β  : V → Y → Set}{d₁ : (u : U) (x : X) → Dec (α u x)}{d₂ : (u : V) (x : Y) → Dec (β u x)} → (u : Σ U (λ x → V)) (x : Σ X (λ x₁ → Y)) → Dec ((α ⊗ᵣ β) u x)
⊗d {U}{V}{X}{Y}{α}{β}{d₁}{d₂} (u , v) (x , y) with d₁ u x | d₂ v y
... | yes z | yes z' = yes (z , z')
... | yes z | no z' = no (λ z'' → z' (snd z''))
... | no z | yes z' = no (λ z'' → z (fst z''))
... | no z | no z' = no (λ z'' → z' (snd z''))

_⊗ₒ_ : (A B : Obj) → Obj
(U , X , n₁ , α , d₁) ⊗ₒ (V , Y , n₂ , β , d₂) = ((U × V) , (X × Y) , trans-× n₁ n₂ , α ⊗ᵣ β , ⊗d {α = α} {β}{d₁}{d₂})

F⊗ : ∀{Z T V X U Y : Set}{F : U → Z → X}{G : V → T → Y} → (U × V) → (Z × T) → (X × Y)
F⊗ {F = F}{G} (u , v) (z , t) = F u z , G v t
  
_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
_⊗ₐ_ {(U , X , _ , α , _)}{(V , Y , _ , β , _)}{(W , Z , _ , γ , _)}{(S , T , _ , δ , _)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {F = F}{G} , p⊗
 where
  p⊗ : {u : Σ U (λ x → V)} {y : Σ Z (λ x → T)} → (α ⊗ᵣ β) u (F⊗ {F = F}{G} u y) → (γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y
  p⊗ {u , v}{z , t} (p₃ , p₄) = p₁  p₃ , p₂ p₄

π₁ : {A B : Obj} → Hom (A ⊗ₒ B) A
π₁ {U , X , n₁ , α , d₁}{V , Y , n₂ , β , d₂} = fst , (λ r x → x , n₂ triv) , cond
 where
   cond : {u : Σ U (λ x → V)} {y : X} → (α ⊗ᵣ β) u (y , n₂ triv) → α (fst u) y
   cond {u , v}{x} (p₁ , p₂) = p₁

π₂ : {A B : Obj} → Hom (A ⊗ₒ B) B
π₂ {U , X , n₁ , α , d₁}{V , Y , n₂ , β , d₂} = snd , (λ r y → n₁ triv , y) , cond
 where
  cond : {u : Σ U (λ x → V)} {y : Y} → (α ⊗ᵣ β) u (n₁ triv , y) → β (snd u) y
  cond {u , v}{y} (p₁ , p₂) = p₂

cart-ar-d : {X Y W Z V : Set}{β : V → Y → Set}{F  : W → X → Z}{G  : W → Y → Z}{g  : W → V}{d₂ : (v' : V) (y' : Y) → Dec (β v' y')} → W → Σ X (λ x → Y) → Z
cart-ar-d {β = β}{F}{G}{g}{d₂} w (x , y) with d₂ (g w) y
... | yes t = F w x
... | no t = G w y

cart-ar : {A B C : Obj}
  → (f : Hom C A)
  → (g : Hom C B)
  → Hom C (A ⊗ₒ B)
cart-ar {U , X , x , α , d₁}{V , Y , y , β , d₂}{W , Z , z , γ , d₃} (f , F , p₁) (g , G , p₂) = trans-× f g ,  cart-ar-d {X}{Y}{W}{Z}{V}{β}{F}{G}{g}{d₂} , cond
 where
   cond : {u : W} {y : Σ X (λ x → Y)} → γ u (cart-ar-d {X}{Y}{W}{Z}{V}{β}{F}{G}{g}{d₂} u y) → (α ⊗ᵣ β) (f u , g u) y
   cond {w}{x , y} p₃ with d₂ (g w) y
   ... | yes t = p₁ p₃ , t
   ... | no t = ⊥-elim (t (p₂ p₃)) , p₂ p₃

-- Cannot prove the following:
-- 
-- cart-diag₁ : ∀{A B C : Obj}
--   → {f : Hom C A}
--   → {g : Hom C B}
--   → (cart-ar f g) ○ π₁ ≡h f
-- cart-diag₁ {U , X , x , α , d₁}{V , Y , y , β , d₂}{W , Z , z , γ , d₃}{f , F , p₁}{g , G , p₂} = ext-set refl , {!!}
--  where
--    aux : (λ u z₁ → cart-ar-d {X} {Y} {W} {Z} {V} {β} {F} {G} {g} {d₂} u (z₁ , y triv)) ≡ F
--    aux = ext-set (λ {w} → ext-set (λ {x₁} → {!!}))
--     where
--      aux' : ∀{w x₁} → cart-ar-d {X} {Y} {W} {Z} {V} {β} {F} {G} {g} {d₂} w (x₁ , y triv) ≡ F w x₁
--      aux' {w}{x₁} with d₂ (g w) (y triv)
--      ... | yes t = refl
--      ... | no t with d₃ w (G w (y triv))
--      ... | yes t' = ⊥-elim (t (p₂ t'))
--      ... | no t' = {!!}

-- cart-diag₂ : ∀{A B C : Obj}
--   → {f : Hom C A}
--   → {g : Hom C B}
--   → (cart-ar f g) ○ π₂ ≡h g
-- cart-diag₂ = {!!}
