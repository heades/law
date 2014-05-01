------------------------------------------------------------------------
-- This file contains the definition of a preorder as a category with --
-- additional properties.                                             --
------------------------------------------------------------------------
module Category.Poset where

open import Level renaming (suc to lsuc)
open import Data.List
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Empty
open import Data.Unit

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

_≇_ : {l : Level}{A B : Set l} → (a : A) → (b : B) → Set l
a ≇ b = (a ≅ b → ⊥)

postulate eq-dec : ∀{l}{A B : Set l} → (a : A) → (b : B) → a ≅ b ⊎ a ≇ b

PosetCat : {l : Level} → (J : Poset {l}) → Cat {l}
PosetCat J = (po-cat (poset-cat J))

PosetObj : {l : Level} → (J : Poset {l}) → Set l
PosetObj J = Obj (PosetCat J)
