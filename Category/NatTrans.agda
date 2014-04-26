----------------------------------------------------------------
-- This file contains the definition natural transformations. --
----------------------------------------------------------------
module Category.NatTrans where

open import Level

open import Category.Category public
open import Category.Funct public 
open import Category.CatEq public

record NatTrans {l₁ l₂ : Level} 
                {ℂ₁ : Cat {l₁}}
                {ℂ₂ : Cat {l₂}} 
                (F G : Functor ℂ₁ ℂ₂) : Set (l₁ ⊔ l₂) where
  field
    -- The family of components.
    η : (A : Obj ℂ₁) → el (Hom ℂ₂ (omap F A) (omap G A))

    -- The natural transformation law.
    η-ax : ∀{A B}{f : el (Hom ℂ₁ A B)} → comm-square {ℂ = ℂ₂} (appT (fmap F) f) (η B) (η A) (appT (fmap G) f)

open NatTrans public
