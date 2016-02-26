module DCBSets where

open import prelude
open import relations

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (Σ[ X ∈ Set ] (Σ[ x ∈ (⊤ → X) ] (Σ[ d ∈ (X × X → X) ](Σ[ α ∈ (U → X → Set) ]( (∀{u : U}{x₁ x₂ : X} → α u (d (x₁ , x₂)) → ((α u x₁) × (α u x₂))) × ( ∀{Y : Set}{x' : X}{F : Y → X}{y : ⊤ → Y} → d (x' , F (y triv)) ≡ x' ) × ( ∀{Y : Set}{x' : X}{F : Y → X}{y : ⊤ → Y} → d (F (y triv) , x') ≡ x'  ))))))

-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , X , x , d₁ , α , p₁ ) (V , Y , y , d₂ , β , p₂) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (U → Y → X) ] ((∀{u : U}{y : Y} → α u (F u y) → β (f u) y)))


-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , x , d₁ , α , dec₁ , p₁ , p₂)} {(V , Y , y , d₂ , β , dec₂ , p₃ , p₄)} {(W , Z , z , d₃ , γ , dec₃ , p₅ , p₆)} (f , F , q₁) (g , G , q₂) =
  g ∘ f , (((λ u z' → F u (G (f u) z')))  ) , (λ {u} {z'} r → q₂ (q₁ r))


infixl 5 _○_

_○_ = comp


-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)


-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , n , d , α , p)} = (id-set , curry snd , id-set)


-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safely ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , X , _ , _ , _ , _ , _ , _)}{(V , Y , _ , β , _ , _ , _ , _)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

≡h-refl : {A B : Obj}{f : Hom A B} → f ≡h f
≡h-refl {U , X , _ , α , _ , _ , _ , _}{V , Y , _ , β , _ , _ , _ , _}{f , F , _} = refl , refl


≡h-trans : ∀{A B}{f g h : Hom A B} → f ≡h g → g ≡h h → f ≡h h
≡h-trans {U , X , _ , α , _ , _ , _ , _}{V , Y , _ , β , _ , _ , _ , _}{f , F , _}{g , G , _}{h , H , _} (p₁ , p₂) (p₃ , p₄) rewrite p₁ | p₂ | p₃ | p₄ = refl , refl

≡h-sym : ∀{A B}{f g : Hom A B} → f ≡h g → g ≡h f
≡h-sym {U , X , _ , α , _ , _ , _ , _}{V , Y , _ , β , _ , _ , _ , _}{f , F , _}{g , G , _} (p₁ , p₂) rewrite p₁ | p₂ = refl , refl

≡h-subst-○ : ∀{A B C}{f₁ f₂ : Hom A B}{g₁ g₂ : Hom B C}{j : Hom A C}
  → f₁ ≡h f₂
  → g₁ ≡h g₂
  → f₂ ○ g₂ ≡h j
  → f₁ ○ g₁ ≡h j
≡h-subst-○ {U , X , _ , α , _ , _ , _ , _}
         {V , Y , _ , β , _ , _ , _ , _}
         {W , Z , _ , γ , _ , _ , _ , _}
         {f₁ , F₁ , _}
         {f₂ , F₂ , _}
         {g₁ , G₁ , _}
         {g₂ , G₂ , _}
         {j , J , _}
         (p₅ , p₆) (p₇ , p₈) (p₉ , p₁₀) rewrite p₅ | p₆ | p₇ | p₈ | p₉ | p₁₀ = refl , refl

○-assoc : ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
  → f ○ (g ○ h) ≡h (f ○ g) ○ h
○-assoc {U , X , _ , α , _ , _ , _ , _}{V , Y , _ , β , _ , _ , _ , _}{W , Z , _ , γ , _ , _ , _ , _}{S , T , _ , ι , _ , _ , _ , _}
        {f , F , _}{g , G , _}{h , H , _} = refl , refl

○-idl : ∀{A B}{f : Hom A B} → id ○ f ≡h f
○-idl {U , X , _ , _ , _ , _ , _ , _}{V , Y , _ , _ , _ , _ , _ , _}{f , F , _} = refl , refl

○-idr : ∀{A B}{f : Hom A B} → f ○ id ≡h f
○-idr {U , X , _ , _ , _ , _ , _ , _}{V , Y , _ , _ , _ , _ , _ , _}{f , F , _} = refl , refl


-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U X V Y : Set} → (U → X → Set) → (V → Y → Set) → ((U × V) → (X × Y) → Set)
_⊗ᵣ_ α β (u , v) (x , y) = (α u x) × (β v y)

_⊗ₒ_ : (A B : Obj) → Obj
(U , X , n₁ , d₁ , α , pr₁ , q₁ , q₂ ) ⊗ₒ (V , Y , n₂ , d₂ , β , pr₂ , q₃ , q₄) = ((U × V) , (X × Y) , trans-× n₁ n₂ ,  d⊗ , (α ⊗ᵣ β) , pr⊗ , ((λ {Y x' F y} → q₁⊗ {Y} {x'}{F}{y}) , (λ {Y x' F y} → q₂⊗ {Y} {x'}{F}{y})))
 where
   d⊗ : Σ (Σ X (λ x → Y)) (λ x → Σ X (λ x₁ → Y)) → Σ X (λ x → Y)
   d⊗ ((x , y) , (x' , y')) = d₁ (x , x') , d₂ (y , y')

   pr⊗ : {u : Σ U (λ x → V)} {x₁ x₂ : Σ X (λ x → Y)} → (α ⊗ᵣ β) u (d⊗ (x₁ , x₂)) → Σ ((α ⊗ᵣ β) u x₁) (λ x → (α ⊗ᵣ β) u x₂)
   pr⊗ {u , v}{x , y}{x' , y'} (p , p') = (fst (pr₁ p) , fst (pr₂ p')) , snd (pr₁ p) , snd (pr₂ p')

   q₁⊗ : {Y₁ : Set} {x' : Σ X (λ x → Y)} {F : Y₁ → Σ X (λ x → Y)}{y : ⊤ → Y₁} → d⊗ (x' , F (y triv)) ≡ x'
   q₁⊗ {_}{x , y}{F}{p} with q₁ {x' = x}{fst ∘ F}{p} | q₃ {x' = y}{snd ∘ F}{p}
   ... | q'₁ | q'₂ with F (p triv)
   ... | x' , y'  rewrite q'₁ | q'₂ = refl

   q₂⊗ : {Y₁ : Set} {x' : Σ X (λ x → Y)} {F : Y₁ → Σ X (λ x → Y)}{y : ⊤ → Y₁} → d⊗ (F (y triv) , x') ≡ x'
   q₂⊗ {Y}{x , y}{F}{p} with q₂ {_}{x}{fst ∘ F}{p} | q₄ {_}{y}{snd ∘ F}{p}
   ... | q'₁ | q'₂ with F (p triv)
   ... | x' , y' rewrite q'₁ | q'₂ = refl


F⊗ : ∀{Z T V X U Y : Set}{F : U → Z → X}{G : V → T → Y} → (U × V) → (Z × T) → (X × Y)
F⊗ {F = F}{G} (u , v) (z , t) = F u z , G v t
  
_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
_⊗ₐ_ {(U , X , _ , _ , α , _ , _ , _)}{(V , Y , _ , _ , β , _ , _ , _)}{(W , Z , _ , _ , γ , _ , _ , _)}{(S , T , _ , _ , δ , _ , _ , _)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {F = F}{G} , p⊗
 where
  p⊗ : {u : Σ U (λ x → V)} {y : Σ Z (λ x → T)} → (α ⊗ᵣ β) u (F⊗ {F = F}{G} u y) → (γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y
  p⊗ {u , v}{z , t} (p₃ , p₄) = p₁  p₃ , p₂ p₄
  

π₁ : {A B : Obj} → Hom (A ⊗ₒ B) A
π₁ {U , X , n₁ , _ , α , _ , _ , _}{V , Y , n₂ , _ , β , _ , _ , _} = fst , (λ r x → x , n₂ triv) , cond
 where
   cond : {u : Σ U (λ x → V)} {y : X} → (α ⊗ᵣ β) u (y , n₂ triv) → α (fst u) y
   cond {u , v}{x} (p₁ , p₂) = p₁


π₂ : {A B : Obj} → Hom (A ⊗ₒ B) B
π₂ {U , X , n₁ , _ , α , _ , _ , _}{V , Y , n₂ , _ , β , _ , _ , _} = snd , (λ r y → n₁ triv , y) , cond
 where
  cond : {u : Σ U (λ x → V)} {y : Y} → (α ⊗ᵣ β) u (n₁ triv , y) → β (snd u) y
  cond {u , v}{y} (p₁ , p₂) = p₂


cart-ar : {A B C : Obj}
  → (f : Hom C A)
  → (g : Hom C B)
  → Hom C (A ⊗ₒ B)
cart-ar {U , X , x , d₁ , α , pr₁ , q₁ , q₂}{V , Y , y ,  d₂ , β , pr₂ , q₃ , q₄}{W , Z , z , d₃ , γ , pr₃ , q₅ , q₆} (f , F , p₁) (g , G , p₂) = trans-× f g ,  crt , cond
 where
  crt : W → Σ X (λ x₁ → Y) → Z
  crt w (x' , y') = d₃ ((F w x') , (G w y'))

  cond : {u : W} {y₁ : Σ X (λ x₁ → Y)} → γ u (crt u y₁) → (α ⊗ᵣ β) (f u , g u) y₁
  cond {w}{x' , y'} p = p₁ (fst (pr₃ {w}{F w x'}{G w y'} p)) , p₂ (snd (pr₃ {w}{F w x'}{G w y'} p))

cart-diag₁ : ∀{A B C : Obj}
  → {f : Hom C A}
  → {g : Hom C B}
  → (cart-ar f g) ○ π₁ ≡h f
cart-diag₁ {U , X , x , d₁ , α , pr₁ , q₁ , q₂}{V , Y , y , d₂ , β , q₃ , q₄ , q₅}{W , Z , z , d₃ , γ , q₆ , q₇ , q₈}{f , F , p₁}{g , G , p₂} = refl , ext-set (λ {w} → ext-set (λ {x} → q₇ {x' = F w x}{G w}{y}))

 
cart-diag₂ : ∀{A B C : Obj}
  → {f : Hom C A}
  → {g : Hom C B}
  → (cart-ar f g) ○ π₂ ≡h g
cart-diag₂ {U , X , x , d₁ , α , pr₁ , q₁ , q₂}{V , Y , y , d₂ , β , q₃ , q₄ , q₅}{W , Z , z , d₃ , γ , q₆ , q₇ , q₈}{f , F , p₁}{g , G , p₂} = refl , ext-set (λ {w} → ext-set (λ {y₁} → q₈ {x' = G w y₁}{F w}{x}))

