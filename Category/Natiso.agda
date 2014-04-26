----------------------------------------------------------------
-- This file contains the definition of natural isomorphisms. --
----------------------------------------------------------------
module Natiso where

open import Category.NatTrans public
open import Category.Iso public

record NatIso {l₁ l₂ : Level} 
              {ℂ₁ : Cat {l₁}}
              {ℂ₂ : Cat {l₂}} 
              (F G : Functor ℂ₁ ℂ₂) : Set (l₁ ⊔ l₂) where
  field
    -- The natural transformation.
    natt : NatTrans F G

    -- Each component of (η natt) is an iso.
    η-iso-ax : ∀{A : Obj ℂ₁} → Iso {l₂}{ℂ₂}{A = omap F A}{omap G A} (η natt A)
    
open NatIso public
