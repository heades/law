------------------------------------------------------------------------
-- This file contains the definition of a preorder as a category with --
-- additional properties.                                             --
------------------------------------------------------------------------
module Category.Preorder where

open import Level renaming (suc to lsuc)

open import Setoid.Total
open import Category.Category

record PO {l : Level} : Set (lsuc l) where
  field
    -- The underlying category.
    ℙ : Cat {l}

    -- The preorder axiom.
    POax : ∀{A B}{f g : el (Hom ℙ A B)} → ⟨ Hom ℙ A B ⟩[ f ≡ g ]

open PO public renaming (ℙ to po-cat)
