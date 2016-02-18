-----------------------------------------------------------------------
-- This file defines DC₂(Sets) and its SMC structure.              --
-----------------------------------------------------------------------
module DC2Sets where

open import prelude

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (Σ[ X ∈ Set ] (U → X → Set))

-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , X , α) (V , Y , β) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (U → Y → X) ] (∀{u : U}{y : Y} → α u (F u y) → β (f u) y))

-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (f , F , p₁) (g , G , p₂) =
  (g ∘ f , (λ u z → F u (G (f u) z)), (λ {u} {y} p₃ → p₂ (p₁ p₃)))

infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , α)} = (id-set , curry snd , id-set)

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safely ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , X , α)}{(V , Y , β)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

≡h-refl : {A B : Obj}{f : Hom A B} → f ≡h f
≡h-refl {U , X , α}{V , Y , β}{f , F , _} = refl , refl

≡h-trans : ∀{A B}{f g h : Hom A B} → f ≡h g → g ≡h h → f ≡h h
≡h-trans {U , X , α}{V , Y , β}{f , F , _}{g , G , _}{h , H , _} (p₁ , p₂) (p₃ , p₄) rewrite p₁ | p₂ | p₃ | p₄ = refl , refl

≡h-sym : ∀{A B}{f g : Hom A B} → f ≡h g → g ≡h f
≡h-sym {U , X , α}{V , Y , β}{f , F , _}{g , G , _} (p₁ , p₂) rewrite p₁ | p₂ = refl , refl

≡h-subst-○ : ∀{A B C}{f₁ f₂ : Hom A B}{g₁ g₂ : Hom B C}{j : Hom A C}
  → f₁ ≡h f₂
  → g₁ ≡h g₂
  → f₂ ○ g₂ ≡h j
  → f₁ ○ g₁ ≡h j
≡h-subst-○ {U , X , α}
         {V , Y , β}
         {W , Z , γ}
         {f₁ , F₁ , _}
         {f₂ , F₂ , _}
         {g₁ , G₁ , _}
         {g₂ , G₂ , _}
         {j , J , _}
         (p₅ , p₆) (p₇ , p₈) (p₉ , p₁₀) rewrite p₅ | p₆ | p₇ | p₈ | p₉ | p₁₀ = refl , refl

○-assoc : ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
  → f ○ (g ○ h) ≡h (f ○ g) ○ h
○-assoc {U , X , α}{V , Y , β}{W , Z , γ}{S , T , ι}
        {f , F , _}{g , G , _}{h , H , _} = refl , refl

○-idl : ∀{A B}{f : Hom A B} → id ○ f ≡h f
○-idl {U , X , _}{V , Y , _}{f , F , _} = refl , refl

○-idr : ∀{A B}{f : Hom A B} → f ○ id ≡h f
○-idr {U , X , _}{V , Y , _}{f , F , _} = refl , refl


-----------------------------------------------------------------------
-- DC₂(Sets) is a SMC                                              --
-----------------------------------------------------------------------

-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U X V Y : Set} → (U → X → Set) → (V → Y → Set) → ((U × V) → (X × Y) → Set)
_⊗ᵣ_ α β (u , v) (x , y) = (α u x) × (β v y)

_⊗ₒ_ : (A B : Obj) → Obj
(U , X , α) ⊗ₒ (V , Y , β) = ((U × V) , (X × Y) , α ⊗ᵣ β)

F⊗ : ∀{Z T V X U Y : Set}{F : U → Z → X}{G : V → T → Y} → (U × V) → (Z × T) → (X × Y)
F⊗ {F = F}{G} (u , v) (z , t) = F u z , G v t
  
_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
_⊗ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {F = F}{G} , p⊗
 where
  p⊗ : {u : Σ U (λ x → V)} {y : Σ Z (λ x → T)} → (α ⊗ᵣ β) u (F⊗ {F = F}{G} u y) → (γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y
  p⊗ {u , v}{z , t} (p₃ , p₄) = p₁  p₃ , p₂ p₄


-- The unit for tensor:
ι : ⊤ → ⊤ → Set
ι triv triv = ⊤

I : Obj
I = (⊤ , ⊤ , ι)

J : Obj
J = (⊤ , ⊤ , (λ x y → ⊥))


-- The left-unitor:
λ⊗-p : ∀{U X α}{u : Σ ⊤ (λ x → U)} {y : X} → (ι ⊗ᵣ α) u (triv , y) → α (snd u) y
λ⊗-p {U}{X}{α}{(triv , u)}{x} = snd
   
λ⊗ : ∀{A : Obj} → Hom (I ⊗ₒ A) A
λ⊗ {(U , X , α)} = snd , (λ _ x → triv , x) , λ⊗-p

λ⊗-inv : ∀{A : Obj} → Hom A (I ⊗ₒ A)
λ⊗-inv {(U , X , α)} = (λ u → triv , u) , (λ _ r → snd r) , λ⊗-inv-p
 where
  λ⊗-inv-p : ∀{U X α}{u : U} {y : Σ ⊤ (λ x → X)} → α u (snd y) → (ι ⊗ᵣ α) (triv , u) y
  λ⊗-inv-p {U}{X}{α}{u}{triv , x} p = triv , p

-- The right-unitor:
ρ⊗ : ∀{A : Obj} → Hom (A ⊗ₒ I) A
ρ⊗ {(U , X , α)} = fst , (λ r x → x , triv) , ρ⊗-p
 where
  ρ⊗-p : ∀{U X α}{u : Σ U (λ x → ⊤)} {y : X} → (α ⊗ᵣ ι) u (y , triv) → α (fst u) y
  ρ⊗-p {U}{X}{α}{(u , _)}{x} (p , _) = p


ρ⊗-inv : ∀{A : Obj} → Hom A (A ⊗ₒ I)
ρ⊗-inv {(U , X , α)} = (λ u → u , triv) , (λ u r → fst r) , ρ⊗-p-inv
 where
  ρ⊗-p-inv : ∀{U X α}{u : U} {y : Σ X (λ x → ⊤)} → α u (fst y) → (α ⊗ᵣ ι) (u , triv) y
  ρ⊗-p-inv {U}{X}{α}{u}{x , triv} p = p , triv

-- Symmetry:
β⊗ : ∀{A B : Obj} → Hom (A ⊗ₒ B) (B ⊗ₒ A)
β⊗ {(U , X , α)}{(V , Y , β)} = twist-× , (λ r₁ r₂ → twist-× r₂) , β⊗-p
 where
   β⊗-p : ∀{U V Y X α β}{u : Σ U (λ x → V)} {y : Σ Y (λ x → X)} → (α ⊗ᵣ β) u (twist-× y) → (β ⊗ᵣ α) (twist-× u) y
   β⊗-p {U}{V}{Y}{X}{α}{β}{u , v}{y , x} = twist-×


-- The associator:
Fα-inv : ∀{ℓ}{U V W X Y Z : Set ℓ} → (U × (V × W)) → ((X × Y) × Z) → (X × (Y × Z))
Fα-inv (u , (v , w)) ((x , y) , z) = x , y , z
   
α⊗-inv : ∀{A B C : Obj} → Hom (A ⊗ₒ (B ⊗ₒ C)) ((A ⊗ₒ B) ⊗ₒ C)
α⊗-inv {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = rl-assoc-× , Fα-inv , α-inv-cond
 where
   α-inv-cond : {u : Σ U (λ x → Σ V (λ x₁ → W))}{y : Σ (Σ X (λ x → Y)) (λ x → Z)}
     → (α ⊗ᵣ (β ⊗ᵣ γ)) u (Fα-inv u y)
     → ((α ⊗ᵣ β) ⊗ᵣ γ) (rl-assoc-× u) y
   α-inv-cond {u , (v , w)}{(x , y) , z} (p₁ , (p₂ , p₃)) = (p₁ , p₂) , p₃


Fα : ∀{V W X Y U Z : Set} → ((U × V) × W) → (X × (Y × Z)) → ((X × Y) × Z)
Fα {V}{W}{X}{Y}{U}{Z} ((u , v) , w) (x , (y , z)) = (x , y) , z

α⊗ : ∀{A B C : Obj} → Hom ((A ⊗ₒ B) ⊗ₒ C) (A ⊗ₒ (B ⊗ₒ C)) 
α⊗ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = (lr-assoc-× , Fα , α-cond)
 where
  α-cond : {u : Σ (Σ U (λ x → V)) (λ x → W)}
      {y : Σ X (λ x → Σ Y (λ x₁ → Z))} →
      ((α ⊗ᵣ β) ⊗ᵣ γ) u (Fα u y) → (α ⊗ᵣ (β ⊗ᵣ γ)) (lr-assoc-× u) y
  α-cond {(u , v) , w}{x , (y , z)} ((p₁ , p₂) , p₃) = p₁ , p₂ , p₃

α⊗-id₁ : ∀{A B C} → (α⊗ {A}{B}{C}) ○ α⊗-inv ≡h id
α⊗-id₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
 where
   aux : {a : Σ (Σ U (λ x → V)) (λ x → W)} → rl-assoc-× (lr-assoc-× a) ≡ a
   aux {(u , v) , w} = refl

   aux' : {a : Σ (Σ U (λ x → V)) (λ x → W)} → (λ z → Fα {V}{W}{X}{Y}{U}{Z} a (Fα-inv (lr-assoc-× a) z)) ≡ (λ y → y)
   aux' {(u , v), w} = ext-set aux''
    where
      aux'' : {a : Σ (Σ X (λ x → Y)) (λ x → Z)} → Fα ((u , v) , w) (Fα-inv (u , v , w) a) ≡ a
      aux'' {(x , y) , z} = refl

α⊗-id₂ : ∀{A B C} → (α⊗-inv {A}{B}{C}) ○ α⊗ ≡h id
α⊗-id₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
 where
   aux : {a : Σ U (λ x → Σ V (λ x₁ → W))} → lr-assoc-× (rl-assoc-× a) ≡ a
   aux {u , (v , w)} = refl
   aux' : {a : Σ U (λ x → Σ V (λ x₁ → W))} → (λ z → Fα-inv {_}{U}{V}{W}{X}{Y}{Z} a (Fα (rl-assoc-× a) z)) ≡ (λ y → y)
   aux' {u , (v , w)} = ext-set aux''
    where
      aux'' : {a : Σ X (λ x → Σ Y (λ x₁ → Z))} → Fα-inv (u , v , w) (Fα ((u , v) , w) a) ≡ a
      aux'' {x , (y , z)} = refl
       
-- Internal hom:
⊸-cond : ∀{U V X Y : Set}{α : U → X → Set}{β : V → Y → Set}
  → Σ (U → V) (λ x → U → Y → X)
  → Σ U (λ x → Y)
  → Set
⊸-cond {α = α}{β} (f , F) (u , y) = α u (F u y) → β (f u) y

_⊸ₒ_ : Obj → Obj → Obj
(U , X , α) ⊸ₒ (V , Y , β) = ((U → V) × (U → Y → X)) , ((U × Y) , ⊸-cond {α = α}{β})


_⊸ₐ_ : {A B C D : Obj} → Hom C A → Hom B D → Hom (A ⊸ₒ B) (C ⊸ₒ D)
_⊸ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) =
  h , H , cond
 where
  h : Σ (U → V) (λ x → U → Y → X) → Σ (W → S) (λ x → W → T → Z)
  h (i , I) = (λ w → g (i (f w))) , (λ w t → F w (I (f w) (G (i (f w)) t)))
  H : Σ (U → V) (λ x → U → Y → X) → Σ W (λ x → T) → Σ U (λ x → Y)
  H (i , I) (w , t) = f w , G (i (f w)) t
  cond : {u : Σ (U → V) (λ x → U → Y → X)} {y : Σ W (λ x → T)} → ⊸-cond {α = α}{β} u (H u y) → ⊸-cond {α = γ}{δ} (h u) y
  cond {i , I}{w , y} p₃ p₄ = p₂ (p₃ (p₁ p₄))

cur : {A B C : Obj}
  → Hom (A ⊗ₒ B) C
  → Hom A (B ⊸ₒ C)
cur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
  = (λ u → (λ v → f (u , v)) , (λ v z → snd (F (u , v) z))) , (λ u r → fst (F (u , (fst r)) (snd r))) , cond 
 where
   cond : {u : U} {y : Σ V (λ x → Z)}
     → α u (fst (F (u , fst y) (snd y)))
     → ⊸-cond {α = β}{γ} ((λ v → f (u , v)) , (λ v z → snd (F (u , v) z))) y   
   cond {u}{v , z} p₂ p₃ with (p₁ {u , v}{z})
   ... | p₄ with F (u , v) z
   ... | (x , y) = p₄ (p₂ , p₃)
   

cur-≡h : ∀{A B C}{f₁ f₂ : Hom (A ⊗ₒ B) C}
  → f₁ ≡h f₂
  → cur f₁ ≡h cur f₂
cur-≡h {U , X , α}{V , Y , β}{W , Z , γ}
       {f₁ , F₁ , p₁}{f₂ , F₂ , p₂} (p₃ , p₄)
       rewrite p₃ | p₄ = refl , refl

cur-cong : ∀{A B C}{f₁ f₂ : Hom (A ⊗ₒ B) C} → f₁ ≡h f₂ → cur f₁ ≡h cur f₂
cur-cong {(U , X , α)} {(V , Y , β)} {(W , Z , γ)}{f₁ , F₁ , _}{f₂ , F₂ , _} (p₁ , p₂) rewrite p₁ | p₂ = refl , refl


uncur : {A B C : Obj}
  → Hom A (B ⊸ₒ C)
  → Hom (A ⊗ₒ B) C
uncur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
  = let h = λ r → fst (f (fst r)) (snd r)
        H = λ r z → F (fst r) (snd r , z) , snd (f (fst r)) (snd r) z
     in h , (H , cond)
 where
  cond : {u : Σ U (λ x → V)} {y : Z} →
      (α ⊗ᵣ β) u (F (fst u) (snd u , y) , snd (f (fst u)) (snd u) y) →
      γ (fst (f (fst u)) (snd u)) y
  cond {u , v}{z} (p₂ , p₃) with p₁ {u} {v , z}
  ... | p₄ with f u
  ... | i , I = p₄ p₂ p₃
  
cur-uncur-bij₁ : ∀{A B C}{f : Hom (A ⊗ₒ B) C}
  → uncur (cur f) ≡h f
cur-uncur-bij₁ {U , X , α}{V , Y , β}{W , Z , γ}{f , F , p₁} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : Σ U (λ x → V)} → f (fst a , snd a) ≡ f a
   aux₁ {u , v} = refl
   aux₂ : {a : Σ U (λ x → V)} → (λ z → fst (F (fst a , snd a) z) , snd (F (fst a , snd a) z)) ≡ F a
   aux₂ {u , v} = ext-set aux₃
    where
      aux₃ : {a : Z} → (fst (F (u , v) a) , snd (F (u , v) a)) ≡ F (u , v) a
      aux₃ {z} with F (u , v) z
      ... | x , y = refl

cur-uncur-bij₂ : ∀{A B C}{g : Hom A (B ⊸ₒ C)}
  → cur (uncur g) ≡h g
cur-uncur-bij₂ {U , X , α}{V , Y , β}{W , Z , γ}{g , G , p₁} = (ext-set aux) , ext-set (ext-set aux')
 where
  aux : {a : U} → ((λ v → fst (g a) v) , (λ v z → snd (g a) v z)) ≡ g a
  aux {u} with g u
  ... | i , I = refl
  aux' : {u : U}{r : Σ V (λ x → Z)} → G u (fst r , snd r) ≡ G u r
  aux' {u}{v , z} = refl
{-
-- The of-course exponential:
!ₒ-cond : ∀{U X : Set}
  → (U → X → Set)
  → U
  → (U → X *)
  → Set
!ₒ-cond α u f = all-pred (α u) (f u)
   
!ₒ : Obj → Obj
!ₒ (U , X , α) = U , (U → X *) , !ₒ-cond α

!-cta : {V Y U X : Set}
  → (Y → X)
  → (U → V)
  → (V → Y *)
  → (U → X *)
!-cta F f g = λ u → list-funct F (g (f u))

!ₐ-cond : ∀{U V Y X : Set}{F : Y → X}{f : U → V}
  → (α : U → X → Set)
  → (β : V → Y → Set)
  → (p : {u : U} {y : Y} → α u (F y) → β (f u) y)
    {u : U}{l : Y *}
  → all-pred (α u) (list-funct F l)
  → all-pred (β (f u)) l
!ₐ-cond _ _ _ {l = []} _ = triv
!ₐ-cond α β p {u}{x :: xs} (p' , p'') = p p' , !ₐ-cond α β p p''     
      
!ₐ : {A B : Obj} → Hom A B → Hom (!ₒ A) (!ₒ B)
!ₐ {U , X , α}{V , Y , β} (f , F , p) = f , !-cta F f , !ₐ-cond α β p

-- Of-course is a comonad:
ε : ∀{A} → Hom (!ₒ A) A
ε {U , X , α} = id-set , (λ x y → [ x ]) , fst

δ-cta : {U X : Set} → (U → 𝕃 (U → 𝕃 X)) → U → 𝕃 X
δ-cta g u = foldr (λ f rest → (f u) ++ rest) [] (g u)
  
δ : ∀{A} → Hom (!ₒ A) (!ₒ (!ₒ A))
δ {U , X , α} = id-set , δ-cta , δ-cond
  where
   δ-cond : {u : U} {l : 𝕃 (U → 𝕃 X)}
     → all-pred (α u) (foldr (λ f → _++_ (f u)) [] l)
     → all-pred (λ f
     → all-pred (α u) (f u)) l
   δ-cond {l = []} _ = triv
   δ-cond {u}{l = x :: l'} p with
     all-pred-append {X}{α u}
                     {x u}
                     {foldr (λ f → _++_ (f u)) [] l'}
                     ∧-unit ∧-assoc
   ... | p' rewrite p' = fst p , δ-cond {u} {l'} (snd p)

-- These diagrams can be found on page 22 of the report.
comonand-diag₁ : ∀{A}
  → (δ {A}) ○ (!ₐ (δ {A})) ≡h (δ {A}) ○ (δ { !ₒ A})
comonand-diag₁ {U , X , α} =
  refl , ext-set (λ {a} → ext-set (λ {a₁} → aux {a₁}{a a₁}))
 where
   aux : ∀{a₁ : U}{l : 𝕃 (U → 𝕃 (U → 𝕃 X))} →
      foldr (λ f → _++_ (f a₁)) []
      (map (λ g u → foldr (λ f → _++_ (f u)) [] (g u)) l)
      ≡
      foldr (λ f → _++_ (f a₁)) [] (foldr (λ f → _++_ (f a₁)) [] l)
   aux {a}{[]} = refl  
   aux {a}{x :: l} rewrite
     sym (foldr-append {l₁ = x a}{foldr (λ f → _++_ (f a)) [] l}{a})
     = cong2 {a = foldr (λ f → _++_ (f a)) [] (x a)}
             _++_
             refl
             (aux {a}{l})

comonand-diag₂ : ∀{A}
  → (δ {A}) ○ (ε { !ₒ A}) ≡h (δ {A}) ○ (!ₐ (ε {A}))
comonand-diag₂ {U , X , α} =
  refl , ext-set (λ {f} → ext-set (λ {a} → aux {a}{f a}))
 where
  aux : ∀{a : U}{l : X *}
    → l ++ [] ≡ foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x y → x :: []) l)
  aux {a}{[]} = refl
  aux {a}{x :: l} with aux {a}{l}
  ... | IH rewrite ++[] l =
    cong2 {a = x} {x} {l}
          {foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x₁ y → x₁ :: []) l)} _::_ refl
          IH
          
module Cartesian where
  π₁ : {U X V Y : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → Hom ((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β))) (!ₒ (U , X , α))
  π₁ {U}{X}{V}{Y}{α}{β} = fst , (λ f → (λ v u → f u) , (λ u v → [])) , π₁-cond
    where
      π₁-cond : ∀{u : Σ U (λ x → V)} {y : U → 𝕃 X} →
        ((λ u₁ f → all-pred (α u₁) (f u₁)) ⊗ᵣ
        (λ u₁ f → all-pred (β u₁) (f u₁)))
        u ((λ v u₁ → y u₁) , (λ u₁ v → [])) →
        all-pred (α (fst u)) (y (fst u))
      π₁-cond {u , v}{f} (p₁ , p₂) = p₁

  π₂ : {U X V Y : Set}
      → {α : U → X → Set}
      → {β : V → Y → Set}
      → Hom ((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β))) (!ₒ (V , Y , β))
  π₂ {U}{X}{V}{Y}{α}{β} = snd , (λ f → (λ v u → []) , (λ u v → f v)) , π₂-cond
      where
        π₂-cond : ∀{u : Σ U (λ x → V)} {y : V → 𝕃 Y} →
          ((λ u₁ f → all-pred (α u₁) (f u₁)) ⊗ᵣ
            (λ u₁ f → all-pred (β u₁) (f u₁)))
              u ((λ v u₁ → []) , (λ u₁ v → y v)) →
            all-pred (β (snd u)) (y (snd u))
        π₂-cond {u , v}{f} (p₁ , p₂) = p₂

  cart-ar-crt : {U X V Y W Z : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {γ : W → Z → Set}
    → Hom (!ₒ (W , Z , γ)) (!ₒ (U , X , α))
    → Hom (!ₒ (W , Z , γ)) (!ₒ (V , Y , β))
    → Σ (V → U → 𝕃 X) (λ x → U → V → 𝕃 Y) → W → 𝕃 Z
  cart-ar-crt  (f , F , p₁) (g , G , p₂) (j₁ , j₂) w = F (j₁ (g w)) w ++ G (j₂ (f w)) w

  cart-ar : {U X V Y W Z : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {γ : W → Z → Set}
    → Hom (!ₒ (W , Z , γ)) (!ₒ (U , X , α))
    → Hom (!ₒ (W , Z , γ)) (!ₒ (V , Y , β))
    → Hom (!ₒ (W , Z , γ)) ((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β)))
  cart-ar {U}{X}{V}{Y}{W}{Z}{α}{β}{γ} (f , F , p₁) (g , G , p₂)
    = (λ w → f w , g w) , cart-ar-crt {α = α}{β} (f , F , p₁) (g , G , p₂) , cart-ar-cond
      where
        cart-ar-cond : ∀{u : W} {y : Σ (V → U → 𝕃 X) (λ x → U → V → 𝕃 Y)} →
          all-pred (γ u) (cart-ar-crt {α = α}{β} (f , F , p₁) (g , G , p₂) y u) →
          ((λ u₁ f₁ → all-pred (α u₁) (f₁ u₁)) ⊗ᵣ
          (λ u₁ f₁ → all-pred (β u₁) (f₁ u₁)))
          (f u , g u) y
        cart-ar-cond {w}{j₁ , j₂} p
          rewrite
            all-pred-append {f = γ w}{F (j₁ (g w)) w}{G (j₂ (f w)) w} ∧-unit ∧-assoc with p
        ... | (a , b) = p₁ a , p₂ b

  cart-diag₁ : {U X V Y W Z : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {γ : W → Z → Set}
    → {f : Hom (W , Z , γ) (U , X , α)}
    → {g : Hom (W , Z , γ) (V , Y , β)}
    → _≡h_ { !ₒ (W , Z , γ)}{ !ₒ (U , X , α)}
      (!ₐ {W , Z , γ}{U , X , α} f)
      (comp { !ₒ (W , Z , γ)}
            {((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β)))}
            { !ₒ (U , X , α)}
            (cart-ar {α = α}{β}{γ} (!ₐ {W , Z , γ}{U , X , α} f) (!ₐ {W , Z , γ}{V , Y , β} g))
            π₁)
  cart-diag₁ {f = f , F , p₁}{g , G , p₂}
    = refl , ext-set (λ {j} → ext-set (λ {w} → sym (++[] (map F (j (f w))))))

  cart-diag₂ : {U X V Y W Z : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {γ : W → Z → Set}
    → {f : Hom (W , Z , γ) (U , X , α)}
    → {g : Hom (W , Z , γ) (V , Y , β)}
    → _≡h_ { !ₒ (W , Z , γ)}{ !ₒ (V , Y , β)}
      (!ₐ {W , Z , γ}{V , Y , β} g)
      (comp { !ₒ (W , Z , γ)}
            {((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β)))}
            { !ₒ (V , Y , β)}
            (cart-ar {α = α}{β}{γ} (!ₐ {W , Z , γ}{U , X , α} f) (!ₐ {W , Z , γ}{V , Y , β} g))
            π₂)
  cart-diag₂ {f = f , F , p₁}{g , G , p₂}
    = refl , ext-set (λ {j} → ext-set (λ {w} → refl))
-}
