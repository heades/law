----------------------------------------------------------------------
-- This file contains constructions of new categories from existing --
-- categories.                                                      --
----------------------------------------------------------------------
module Category.CategoryCons where

open import Level
open import Data.Product

open import Setoid.Total
open import Category.Category

open SetoidFun

-- The product of two categories.
_●_ : {l₁ l₂ : Level} → (ℂ₁ : Cat {l₁}) → (ℂ₂ : Cat {l₂}) → Cat {l₁ ⊔ l₂}
ℂ₁ ● ℂ₂ = record {
            Obj = (Obj ℂ₁) × (Obj ℂ₂);
            Hom = λ A B → (Hom ℂ₁ (proj₁ A) (proj₁ B)) ●ₛ ((Hom ℂ₂ (proj₂ A) (proj₂ B)));
            comp = λ {A} {B} {C} → (comp ℂ₁) ●b (comp ℂ₂);
            id = λ {A} → (id ℂ₁) , (id ℂ₂);
            assocPf = λ {A} {B} {C} {D} {f} {g} {h} → (assocPf ℂ₁) , (assocPf ℂ₂);
            idPf = λ {A} {B} {f} → (idPf ℂ₁) , (idPf ℂ₂) }
