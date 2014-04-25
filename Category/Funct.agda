--------------------------------------------------------------------
-- This file contains the definition of and facts about functors. --
--------------------------------------------------------------------
module Category.Funct where

open import Level

open import Setoid.Total
open import Category.Category

open SetoidFun

record Functor {l₁ l₂ : Level} (ℂ₁ : Cat {l₁}) (ℂ₂ : Cat {l₂}) : Set (l₁ ⊔ l₂) where
  field
    -- The object map.
    omap : Obj ℂ₁ → Obj ℂ₂
    -- The morphism map.
    fmap : {A B : Obj ℂ₁} 
      → SetoidFun (Hom ℂ₁ A B) (Hom ℂ₂ (omap A) (omap B))

    -- The morphism map must send identities to identities.
    idPF : ∀{A} 
      → ⟨  Hom ℂ₂ (omap A) (omap A) ⟩[ appT fmap (id ℂ₁) ≡ id ℂ₂ ] 
    -- The morphism map must respect composition.
    compPF : ∀{A B}{f g} 
      → ⟨ Hom ℂ₂ (omap A) (omap B) ⟩[ appT fmap (f ○[ comp ℂ₁ {A}{B} ] g) ≡ (appT fmap f) ○[ comp ℂ₂ ] (appT fmap g) ]
