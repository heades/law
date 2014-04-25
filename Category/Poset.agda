------------------------------------------------------------------------
-- This file contains the definition of a preorder as a category with --
-- additional properties.                                             --
------------------------------------------------------------------------
module Category.Poset where

open import Level renaming (suc to lsuc)

open import Setoid.Total
open import Category.Category
open import Category.Preorder
open import Equality.Eq

record Poset {l : Level} : Set (lsuc l) where
  field
    -- The underlying category.
    𝕊 : PO {l}

    -- The poset axiom.
    PSax : ∀{A B}{f : el (Hom (po-cat 𝕊) A B)}{g : el (Hom (po-cat 𝕊) B A)} → A ≅ B

open Poset public renaming (𝕊 to poset-cat)

