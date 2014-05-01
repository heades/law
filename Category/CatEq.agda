-----------------------------------------------------------------------------------
-- This file contains facts about equational reasoning pertaining to categories. --
-----------------------------------------------------------------------------------
module Category.CatEq where

open import Level

open import Category.Category
open import Setoid.Total

-- The following models the communative square:
--
--  A ---f₁---> C
--  |           |
--  f₃          f₂
--  |           |
‌--  V           V
--  D ---f₄---> D
-- 
-- However, as an equation.
comm-square : {l : Level}{ℂ : Cat {l}}{A B D C : Obj ℂ} 
            → el (Hom ℂ A B) 
            → el (Hom ℂ B C) 
            → el (Hom ℂ A D) 
            → el (Hom ℂ D C) 
            → Set l
comm-square {ℂ = ℂ}{A}{C = C} f₁ f₂ f₃ f₄ = ⟨ Hom ℂ A C ⟩[ f₁ ○[ comp ℂ ] f₂ ≡ f₃ ○[ comp ℂ ] f₄ ]
