module Category.Test where
  open import Equality.Eq

  postulate A : Set
  postulate o : A → A
  postulate x : A
  postulate y : A
  postulate h : A → A → Set 
  postulate f : h x y
  postulate I : A
  postulate i : h I I
  postulate m : h x y → h (o x) (o y)
  postulate pf₁ : o x ≅ I
  postulate pf₂ : o y ≅ I

  subst≅2 : {A : Set }{a a' b b' : A}{P : A → A → Set} → a ≅ a' → b ≅ b' → P a b → P a' b'
  subst≅2 refl refl x = x

  eq-f-i-m : Set
  eq-f-i-m = let i-m = let h-pf = eqApp2 pf₁ pf₂ (λ A B → h A B) in subst≅2 {A}{I}{(o x)}{I}{(o y)}{h} (sym pf₁) (sym pf₂) i in m f ≅ i-m
