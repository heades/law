-------------------------------------------
-- This file contains basic definitions. --
-------------------------------------------
module Basics where

  open import Level
  
  data ⊥-poly {l : Level} : Set l where

  ⊥-poly-elim : ∀ {l w} {Whatever : Set w} → ⊥-poly {l} → Whatever
  ⊥-poly-elim ()    
