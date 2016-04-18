-----------------------------------------------------------------------
-- This file defines Degenerate Dial₂(Sets) and shows that it is a   --
-- CCC.                                                              --
-----------------------------------------------------------------------
module DeDial2Sets where

open import prelude

data UnitType : Set₁ where  
  unit : UnitType
  mod : UnitType
  -- comp : UnitType → UnitType → UnitType

⟦_⟧ : UnitType → Set
⟦ unit ⟧ = ⊤
⟦ mod ⟧ = (⊤ *) × (⊤ *)
-- ⟦ comp t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

Obj⊤ : Set₁
Obj⊤ = Σ[ U ∈ Set ] (Σ[ X ∈ UnitType ](U → ⟦ X ⟧ → Set))

Hom⊤ : Obj⊤ → Obj⊤ → Set
Hom⊤ (U , X , α) (V , Y , β) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈  (⟦ Y ⟧ → ⟦ X ⟧) ] (∀{u : U}{y : ⟦ Y ⟧} → α u (F y) → β (f u) y))

comp⊤ : {A B C : Obj⊤} → Hom⊤ A B → Hom⊤ B C → Hom⊤ A C
comp⊤ {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (f , F , p₁) (g , G , p₂) =
  (g ∘ f , F ∘ G , (λ {u z} p-α → p₂ (p₁ p-α)))

infixl 5 _○⊤_

_○⊤_ = comp⊤

-- The contravariant hom-functor:
Hom⊤ₐ :  {A' A B B' : Obj⊤} → Hom⊤ A' A → Hom⊤ B B' → Hom⊤ A B → Hom⊤ A' B'
Hom⊤ₐ f h g = comp⊤ f (comp⊤ g h)

-- The identity function:
id⊤ : {A : Obj⊤} → Hom⊤ A A 
id⊤ {(U , X , α)} = (id-set , id-set , id-set)


-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safly ignore it.
infix 4 _≡h⊤_

_≡h⊤_ : {A B : Obj⊤} → (f g : Hom⊤ A B) → Set
_≡h⊤_ {(U , X , α)}{(V , Y , β)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

≡h⊤-refl : {A B : Obj⊤}{f : Hom⊤ A B} → f ≡h⊤ f
≡h⊤-refl {U , X , α}{V , Y , β}{f , F , _} = refl , refl

≡h⊤-trans : ∀{A B}{f g h : Hom⊤ A B} → f ≡h⊤ g → g ≡h⊤ h → f ≡h⊤ h
≡h⊤-trans {U , X , α}{V , Y , β}{f , F , _}{g , G , _}{h , H , _} (p₁ , p₂) (p₃ , p₄) rewrite p₁ | p₂ | p₃ | p₄ = refl , refl

≡h⊤-sym : ∀{A B}{f g : Hom⊤ A B} → f ≡h⊤ g → g ≡h⊤ f
≡h⊤-sym {U , X , α}{V , Y , β}{f , F , _}{g , G , _} (p₁ , p₂) rewrite p₁ | p₂ = refl , refl


≡h⊤-subst-○ : ∀{A B C : Obj⊤}{f₁ f₂ : Hom⊤ A B}{g₁ g₂ : Hom⊤ B C}{j : Hom⊤ A C}
  → f₁ ≡h⊤ f₂
  → g₁ ≡h⊤ g₂
  → f₂ ○⊤ g₂ ≡h⊤ j
  → f₁ ○⊤ g₁ ≡h⊤ j
≡h⊤-subst-○ {U , X , α}
         {V , Y , β}
         {W , Z , γ}
         {f₁ , F₁ , _}
         {f₂ , F₂ , _}
         {g₁ , G₁ , _}
         {g₂ , G₂ , _}
         {j , J , _}
         (p₅ , p₆) (p₇ , p₈) (p₉ , p₁₀) rewrite p₅ | p₆ | p₇ | p₈ | p₉ | p₁₀ = refl , refl

○⊤-assoc : ∀{A B C D}{f : Hom⊤ A B}{g : Hom⊤ B C}{h : Hom⊤ C D}
  → f ○⊤ (g ○⊤ h) ≡h⊤ (f ○⊤ g) ○⊤ h
○⊤-assoc {U , X , α}{V , Y , β}{W , Z , γ}{S , T , ι}
        {f , F , _}{g , G , _}{h , H , _} = refl , refl


○⊤-idl : ∀{A B}{f : Hom⊤ A B} → id⊤ ○⊤ f ≡h⊤ f
○⊤-idl {U , X , _}{V , Y , _}{f , F , _} = refl , refl


○⊤-idr : ∀{A B}{f : Hom⊤ A B} → f ○⊤ id⊤ ≡h⊤ f
○⊤-idr {U , X , _}{V , Y , _}{f , F , _} = refl , refl

_⊗ᵣ_ : ∀{U V : Set}{X Y : UnitType} → (α : U → ⟦ X ⟧ → Set) → (β : V → ⟦ Y ⟧ → Set) → Σ U (λ x → V) → Σ ⟦ X ⟧ (λ x → ⟦ Y ⟧) → Set
(α ⊗ᵣ β) (u , v) (l₁ , l₂) = (α u l₁) × (β v l₂)

_⊗ₒ_ : (A B : Obj⊤) → Obj⊤
(U , unit , α) ⊗ₒ (V , unit , β) = (U × V) , unit , (λ p t → (α (fst p) triv) × (β (snd p) triv))
(U , unit , α) ⊗ₒ (V , mod , β) = (U × V) , (mod , (λ p t → (α (fst p) triv) × (β (snd p) t)))
(U , mod , α) ⊗ₒ (V , unit , β) = (U × V) , (mod , (λ p t → (α (fst p) t) × (β (snd p) triv)))
(U , mod , α) ⊗ₒ (V , mod , β) = (U × V) , (mod , (λ p t → (α (fst p) t) × (β (snd p) t)))

-- F⊗ : ∀{S Z W T V X U Y : Set ℓ}{f : U → W}{F : Z → X}{g : V → S}{G : T → Y} → (S → Z) × (W → T) → (V → X) × (U → Y)
-- F⊗ {f = f}{F}{g}{G} (h₁ , h₂) = (λ v → F(h₁ (g v))) , (λ u → G(h₂ (f u)))
  
-- _⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
-- _⊗ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {f = f}{F}{g}{G} , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : Σ U (λ x → V)} {y : Σ (S → Z) (λ x → W → T)} →
--       ((α ⊗ᵣ β) u (F⊗ {f = f}{F}{g}{G} y)) ≤L ((γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y)
--   cond {u , v}{h , j} = l-mul-funct {p = mproset l-pf} (p₁ {u}{h (g v)}) (p₂ {v}{j (f u)})
  
-- □ᵣ : {U : Set}{X : UnitType} → (U → ⟦ X ⟧ → Set) → U → 𝕃 ⟦ X ⟧ → Set
-- □ᵣ α u [] = ⊤
-- □ᵣ {U}{X} α u (x :: l) = (α u x) × (□ᵣ {U}{X} α u l)

-- □ₒ : Obj⊤ → Obj⊤
-- □ₒ (U , X , α) = U , seq X , □ᵣ {U}{X} α

-- □ₐ : {A B : Obj⊤} → Hom⊤ A B → Hom⊤ (□ₒ A) (□ₒ B)
-- □ₐ {U , n₁ , α}{V , n₂ , β} (f , F , p) = f , map F , {!!}
  
π₁ : {A B : Obj⊤} → Hom⊤ (A ⊗ₒ B) A
π₁ {U , unit , α} {V , unit , β} = fst , id-set , (λ {u y} → aux {u}{y})
 where
   aux : {u : Σ U (λ x → V)} {y : ⊤} → Σ (α (fst u) triv) (λ x → β (snd u) triv) → α (fst u) y
   aux {u , v}{triv} = fst
   
π₁ {U , mod , α} {V , unit , β} = fst , id-set , (λ {u y} → aux {u}{y})
 where
  aux : {u : Σ U (λ x → V)} {y : Σ (𝕃 ⊤) (λ x → 𝕃 ⊤)} → Σ (α (fst u) y) (λ x → β (snd u) triv) → α (fst u) y
  aux {u , v}{l₁ , l₂} = fst
  
π₁ {U , unit , α} {V , mod , β} = fst , (λ x → [ x ] , [ x ]) , (λ {u y} → aux {u}{y})
 where
   aux : {u : Σ U (λ x → V)} {y : ⊤} → Σ (α (fst u) triv) (λ x → β (snd u) (y :: [] , y :: [])) → α (fst u) y
   aux {u , v}{triv} = fst

π₁ {U , mod , α} {V , mod , β} = fst , id-set , (λ {u y} → aux {u}{y})
 where
   aux : {u : Σ U (λ x → V)} {y : Σ (𝕃 ⊤) (λ x → 𝕃 ⊤)} → Σ (α (fst u) y) (λ x → β (snd u) y) → α (fst u) y
   aux {u , v}{l} = fst

π₂ : {A B : Obj⊤} → Hom⊤ (A ⊗ₒ B) B
π₂ {U , unit , α} {V , unit , β} = snd , {!!} , {!!}
π₂ {U , mod , α} {V , unit , β} = snd , {!!} , {!!}  
π₂ {U , unit , α} {V , mod , β} = snd , {!!} , {!!}
π₂ {U , mod , α} {V , mod , β} = snd , {!!} , {!!}

postulate rel-++ : ∀{W : Set}{w : W}{γ  : W → 𝕃 (⊤ {lzero}) → Set}{l₁ l₂ : 𝕃 ⊤} → γ w (l₁ ++ l₂) → ((γ w l₁) × (γ w l₂))

cart-ar : {A B C : Obj⊤}
  → (f : Hom⊤ C A)
  → (g : Hom⊤ C B)
  → Hom⊤ C (A ⊗ₒ B)
cart-ar {U , unit , α} {V , unit , β} {W , unit , γ} (f , F , p₁) (g , G , p₂) = trans-× f g , id-set , (λ {u y} → aux {u}{y})
 where
   aux : {u : W} {y : ⊤} → γ u y → Σ (α (f u) triv) (λ x → β (g u) triv)
   aux {w}{triv} p with p₁ {w}{triv} | p₂ {w}{triv}
   ... | p₃ | p₄ with F triv | G triv
   ... | triv | triv = p₃ p , p₄ p

cart-ar {U , unit , α} {V , unit , β} {W , mod , γ} (f , F , p₁) (g , G , p₂) = trans-× f g , (λ x → (fst (F x)) ++ (snd (F x)) , (fst (G x)) ++ (snd (G x))) , {!!}

cart-ar {U , unit , α} {V , mod , β} {W , unit , γ} (f , F , p₁) (g , G , p₂) = trans-× f g , {!!} , {!!}

cart-ar {U , unit , α} {V , mod , β} {W , mod , γ} (f , F , p₁) (g , G , p₂) = trans-× f g , {!!} , {!!}

cart-ar {U , mod , α} {V , unit , β} {W , unit , γ} (f , F , p₁) (g , G , p₂) = trans-× f g , {!!} , {!!}

cart-ar {U , mod , α} {V , unit , β} {W , mod , γ} (f , F , p₁) (g , G , p₂) = trans-× f g , {!!} , {!!}
   
cart-ar {U , mod , α} {V , mod , β} {W , unit , γ} (f , F , p₁) (g , G , p₂) = trans-× f g , {!!} , {!!}
  
cart-ar {U , mod , α} {V , mod , β} {W , mod , γ} (f , F , p₁) (g , G , p₂) = trans-× f g , {!!} , {!!}
   
cart-diag₁ : ∀{A B C : Obj⊤}
  → {f : Hom⊤ C A}
  → {g : Hom⊤ C B}
  → (cart-ar f g) ○⊤ π₁ ≡h⊤ f
cart-diag₁ {U , unit , α} {V , unit , β} {W , unit , γ} {f , F , p₁} {g , G , p₂} = refl , {!!}
cart-diag₁ {U , unit , α} {V , unit , β} {W , mod , γ} {f , F , p₁} {g , G , p₂} = refl , {!!}
cart-diag₁ {U , unit , α} {V , mod , β} {W , unit , γ} {f , F , p₁} {g , G , p₂} = {!!}
cart-diag₁ {U , unit , α} {V , mod , β} {W , mod , γ} {f , F , p₁} {g , G , p₂} = {!!}
cart-diag₁ {U , mod , α} {V , unit , β} {W , unit , γ} {f , F , p₁} {g , G , p₂} = {!!}
cart-diag₁ {U , mod , α} {V , unit , β} {W , mod , γ} {f , F , p₁} {g , G , p₂} = {!!}
cart-diag₁ {U , mod , α} {V , mod , β} {W , unit , γ} {f , F , p₁} {g , G , p₂} = {!!}
cart-diag₁ {U , mod , α} {V , mod , β} {W , mod , γ} {f , F , p₁} {g , G , p₂} = {!!}

-- cart-diag₂ : ∀{A B C : Obj⊤}
--   → {f : Hom (toObj C) (toObj A)}
--   → {g : Hom (toObj C) (toObj B)}
--   → (cart-ar f g) ○ π₂ ≡h g
-- cart-diag₂ {U , α}{V , β}{W , γ}{f , F , p₁}{g , G , p₂} = refl , ext-set ctr
--  where
--    ctr : {a : ⊤} → triv ≡ G a
--    ctr {triv} with G triv
--    ... | triv = refl

-- □ₒ-cond : ∀{U X : Set}
--   → (U → X → Set)
--   → U
--   → (X *)
--   → Set
-- □ₒ-cond {U} α u l = all-pred (α u) l 

-- fromObj : (A : Obj) → Σ[ B ∈ Obj⊤ ]( A ≡ toObj(B)) → Obj⊤
-- fromObj _ ((a , b) , b₁) = a , b 

-- □ₒ : Obj → Obj
-- □ₒ (U , X , α) = (U , X * , □ₒ-cond α)

-- □ₐ : {A B : Obj} → Hom A B → Hom (□ₒ A) (□ₒ B)
-- □ₐ {U , X , α}{V , Y , β} (f , F , p) = f , map F , cond
--  where
--   cond : {u : U} {y : 𝕃 Y} → all-pred (α u) (map F y) → all-pred (β (f u)) y
--   cond {y = []} x = triv
--   cond {y = x :: y} (a , b) = p a , cond b

-- □-ε : ∀{A : Obj} → Hom (□ₒ A) A
-- □-ε {U , X , α} = id-set , (λ x → [ x ] ) , aux
--  where
--   aux : {u : U} {y : X} → Σ (α u y) (λ x → ⊤) → α u y
--   aux (a , b) = a

-- □-δ : ∀{A : Obj} → Hom (□ₒ A) (□ₒ (□ₒ A))
-- □-δ {U , X , α} = id-set , (foldr _++_ []) , cond
--  where
--    cond : {u : U} {y : 𝕃 (𝕃 X)} → all-pred (α u) (foldr _++_ [] y) → all-pred (λ l → all-pred (α u) l) y
--    cond {y = []} p = triv
--    cond {u}{y = y :: y₁} p rewrite
--      (all-pred-append {X}{α u}{y}{foldr _++_ [] y₁} ∧-unit ∧-assoc)
--      with p
--    ... | p₁ , p₂ = p₁ , cond p₂

-- comonand-diag₁ : ∀{A : Obj}
--   → (□-δ {A}) ○ (□ₐ (□-δ {A})) ≡h (□-δ {A}) ○ (□-δ { □ₒ (A)})
-- comonand-diag₁ {U , X , α} = refl , ext-set (λ {a} → ctr {a})
--  where
--   ctr : {a : 𝕃 (𝕃 (𝕃 X))} → foldr _++_ [] (map (foldr _++_ []) a) ≡ foldr _++_ [] (foldr _++_ [] a)
--   ctr {[]} = refl
--   ctr {a :: a₁} rewrite sym (foldr-append {l₁ = a}{foldr _++_ [] a₁}) | ctr {a₁} = refl

-- comonand-diag₂ : ∀{A : Obj}
--   → (□-δ {A}) ○ (□-ε { □ₒ A}) ≡h (□-δ {A}) ○ (□ₐ (□-ε {A}))
-- comonand-diag₂ {U , X , α} = refl , ext-set (λ {a} → cond {a})
--  where
--    cond : {a : 𝕃 X} → a ++ [] ≡ foldr _++_ [] (map (λ x → x :: []) a)
--    cond {a} rewrite ++[] a = foldr-map

-- □-ctr : {U V : Set} → 𝕃 (Σ (V → ⊤) (λ x → U → ⊤)) → Σ (V → 𝕃 ⊤) (λ x → U → 𝕃 ⊤)
-- □-ctr [] = (λ x → [ triv ]) , (λ x → [ triv ])
-- □-ctr ((a , b) :: l) = (λ v → a v :: (fst (□-ctr l)) v) , (λ u → b u :: (snd (□-ctr l)) u)
  
-- □-m : {A B : Obj⊤} → Hom ((□ₒ (toObj A)) ⊗ₒ (□ₒ (toObj B))) (□ₒ ((toObj A) ⊗ₒ (toObj B)))
-- □-m {U , α}{V , β} = id-set , □-ctr , cond
--  where  
--   cond : {u : Σ U (λ x → V)} {y : 𝕃 (Σ (V → ⊤) (λ x → U → ⊤))} →
--       ((λ u₁ l → all-pred (α u₁) l) ⊗ᵣ (λ u₁ l → all-pred (β u₁) l)) u
--       (□-ctr y) → all-pred ((α ⊗ᵣ β) u) y
--   cond {a , b} {[]} x = triv
--   cond {a , b} {(a₁ , b₁) :: y} ((a₂ , b₂) , a₃ , b₃) with cond {a , b}{y}
--   ... | IH with □-ctr y
--   ... | c , d = (a₂ , a₃) , IH (b₂ , b₃)

-- □-m-nat : ∀{A A' B B' : Obj⊤}
--   → (f : Hom (toObj A) (toObj A'))
--   → (g : Hom (toObj B) (toObj B'))
--   → ((□ₐ f) ⊗ₐ (□ₐ g)) ○ □-m ≡h □-m ○ (□ₐ (f ⊗ₐ g))
-- □-m-nat {U , α}{U' , α'}{V , β}{V' , β'} (f , F , p₁) (g , G , p₂) = refl , ext-set (λ {a} → aux {a})
--   where
--     aux : {a : 𝕃 (Σ (V' → ⊤) (λ x → U' → ⊤))} → F⊗ {V'}{𝕃 ⊤}{U'}{𝕃 ⊤}{V}{𝕃 ⊤}{U}{𝕃 ⊤}{f}{map F}{g}{map G} (□-ctr a) ≡ □-ctr (map (F⊗ {V'} {⊤} {U'} {⊤} {V} {⊤} {U} {⊤} {f} {F} {g} {G}) a)
--     aux {[]} with G triv | F triv
--     ... | triv | triv = refl
--     aux {(a , b) :: a₁} = eq-× (ext-set aux₁) (ext-set aux₄)
--      where
--        aux₂ : ∀{v}{l : 𝕃 (Σ (V' → ⊤) (λ x → U' → ⊤))} → map F (fst (□-ctr l) (g v)) ≡ fst (□-ctr (map (F⊗ {V'} {⊤} {U'} {⊤} {V} {⊤} {U} {⊤} {f} {F} {g} {G}) l)) v
--        aux₂ {_}{[]} with F triv
--        ... | triv = refl
--        aux₂ {v}{(a₂ , b₁) :: l} rewrite aux₂ {v}{l} = refl
         
--        aux₁ : {a₂ : V} → F (a (g a₂)) :: map F (fst (□-ctr a₁) (g a₂)) ≡ F (a (g a₂)) :: fst (□-ctr (map (F⊗ {V'} {⊤} {U'} {⊤} {V} {⊤} {U} {⊤} {f} {F} {g} {G}) a₁)) a₂
--        aux₁ {v} with F (a (g v))
--        ... | triv rewrite aux₂ {v}{a₁} = refl

--        aux₃ : ∀{u l} → map G (snd (□-ctr l) (f u)) ≡ snd (□-ctr (map (F⊗ {V'} {⊤} {U'} {⊤} {V} {⊤} {U} {⊤} {f} {F} {g} {G}) l)) u
--        aux₃ {u}{[]} with G triv
--        ... | triv = refl
--        aux₃ {u}{(a₂ , b₁) :: l} rewrite aux₃ {u}{l} = refl

--        aux₄ : {a₂ : U} → G (b (f a₂)) :: map G (snd (□-ctr a₁) (f a₂)) ≡ G (b (f a₂)) :: snd (□-ctr (map (F⊗ {V'} {⊤} {U'} {⊤} {V} {⊤} {U} {⊤} {f} {F} {g} {G}) a₁)) a₂
--        aux₄ {u} rewrite aux₃ {u}{a₁} = refl
       
-- □-m-I : Hom I (□ₒ I)
-- □-m-I = id-set , (λ _ → triv) , cond
--  where
--   cond : {u : ⊤} {y : 𝕃 ⊤} → ι u triv → all-pred (ι u) y
--   cond {triv} {[]} x = triv
--   cond {triv} {triv :: y} triv = triv , cond triv

-- π-□-ctr : {U V : Set} → 𝕃 ⊤ → Σ (V → 𝕃 ⊤) (λ _ → U → 𝕃 ⊤)
-- π-□-ctr [] = (λ x → [ triv ]) , (λ x → [ triv ])
-- π-□-ctr {U}{V} (triv :: l) = (λ v → triv :: fst (π-□-ctr {U}{V} l) v) , ((λ v → triv :: snd (π-□-ctr {U}{V} l) v))

-- π₁-□ : ∀{U α V β} → Hom ((□ₒ (U , ⊤ , α)) ⊗ₒ (□ₒ (V , ⊤ , β))) (□ₒ (U , ⊤ , α))
-- π₁-□ {U}{α}{V}{β} = fst , π-□-ctr , cond
--  where
--    cond : {u : Σ U (λ x → V)} {y : 𝕃 ⊤} →
--       ((λ u₁ l → all-pred (α u₁) l) ⊗ᵣ (λ u₁ l → all-pred (β u₁) l)) u
--       (π-□-ctr y) →
--       all-pred (α (fst u)) y
--    cond {a , b} {[]} x = triv
--    cond {a , b} {triv :: y} ((a₁ , b₁) , a₂ , b₂) with cond {a , b} {y}
--    ... | IH with π-□-ctr {U}{V} y
--    ... | c , d = a₁ , IH (b₁ , b₂)
   
-- □-prod₁ : ∀{U α V β} → _≡h_ {((□ₒ (U , ⊤ , α)) ⊗ₒ (□ₒ (V , ⊤ , β)))}
--                             {(□ₒ (U , ⊤ , α))}
--                             (_○_ {(□ₒ (U , ⊤ , α)) ⊗ₒ (□ₒ (V , ⊤ , β))}{□ₒ ((U , ⊤ , α) ⊗ₒ (V , ⊤ , β))}{□ₒ (U , ⊤ , α)} (□-m {U , α}{V , β}) (□ₐ {(U , ⊤ , α) ⊗ₒ (V , ⊤ , β)}{U , ⊤ , α} (π₁ {U , α}{V , β})))
--                             (π₁-□ {U}{α}{V}{β})
-- □-prod₁ {U}{α}{V}{β} = refl , ext-set (λ {a} → aux {a})
--  where
--   aux : {a : 𝕃 ⊤} → □-ctr {U}{V} (map π-ctr a) ≡ π-□-ctr a
--   aux {[]} = refl
--   aux {triv :: a} rewrite aux {a} = refl

-- π₂-□ : ∀{U α V β} → Hom ((□ₒ (U , ⊤ , α)) ⊗ₒ (□ₒ (V , ⊤ , β))) (□ₒ (V , ⊤ , β))
-- π₂-□ {U}{α}{V}{β} = snd , π-□-ctr , cond
--  where
--    cond : {u : Σ U (λ x → V)} {y : 𝕃 ⊤} →
--       ((λ u₁ l → all-pred (α u₁) l) ⊗ᵣ (λ u₁ l → all-pred (β u₁) l)) u
--       (π-□-ctr y) →
--       all-pred (β (snd u)) y
--    cond {a , b} {[]} x = triv
--    cond {a , b} {triv :: y} ((a₁ , b₁) , a₂ , b₂) with cond {a , b}{y}
--    ... | IH with π-□-ctr {U}{V} y
--    ... | c , d = a₂ , (IH (b₁ , b₂))

-- □-prod₂ : ∀{U α V β} → _≡h_ {((□ₒ (U , ⊤ , α)) ⊗ₒ (□ₒ (V , ⊤ , β)))}
--                             {(□ₒ (V , ⊤ , β))}
--                             (_○_ {(□ₒ (U , ⊤ , α)) ⊗ₒ (□ₒ (V , ⊤ , β))}{□ₒ ((U , ⊤ , α) ⊗ₒ (V , ⊤ , β))}{□ₒ (V , ⊤ , β)} (□-m {U , α}{V , β}) (□ₐ {(U , ⊤ , α) ⊗ₒ (V , ⊤ , β)}{V , ⊤ , β} (π₂ {U , α}{V , β})))
--                             (π₂-□ {U}{α}{V}{β})
-- □-prod₂ {U}{α}{V}{β} = refl , (ext-set (λ {a} → aux {a}))
--  where
--   aux : {a : 𝕃 ⊤} → □-ctr {U}{V} (map π-ctr a) ≡ π-□-ctr a
--   aux {[]} = refl
--   aux {triv :: a} rewrite aux {a} = refl

-- cart-ar-□ : {A B C : Obj⊤}
--   → (f : Hom (□ₒ (toObj C)) (□ₒ (toObj A)))
--   → (g : Hom (□ₒ (toObj C)) (□ₒ (toObj B)))
--   → Hom (□ₒ (toObj C)) ((□ₒ (toObj A)) ⊗ₒ (□ₒ (toObj B)))
-- cart-ar-□ {U , α}{V , β}{W , γ} (f , F , p₁) (g , G , p₂) = trans-× f g ,  {!!} , {!!}
--  where
   
-- -}
