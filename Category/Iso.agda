----------------------------------------------------------------
-- This file contains the definition of isomorphisms.         --
----------------------------------------------------------------
module Category.Iso where

open import Category.Category

record Iso {l : Level}{ℂ : Cat {l}}{A B : Obj ℂ} (f : el (Hom ℂ A B)) : Set l where
  field
    inv : el (Hom ℂ B A)

    left-inv-ax  : ⟨ Hom ℂ A A ⟩[ f ○[ comp ℂ ] inv ≡ id ℂ ]
    right-inv-ax : ⟨ Hom ℂ B B ⟩[ inv ○[ comp ℂ ] f ≡ id ℂ ]

open Iso public
