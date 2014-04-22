-------------------------------------------------------------------------
-- The contents of this file is based on the work in "Setoids in Type  --
-- Theory" by Barthe et. al.                                           --
-- See http://www.cs.ru.nl/~venanzio/publications/Setoids_JFP_2003.pdf --
-------------------------------------------------------------------------
module Setoid.Total where

open import level
open import Relation

-- Total setoids.
record Setoid {l : level} : Set (lsuc l) where
 field 
   el : Set l
   R  : el → el → Set l
   eqRpf : EqRel R

open Setoid

-- Notation for the underlying equivalence of a setoid.
⟨_⟩[_≡_] : {l : level} → (A : Setoid {l}) → el A → el A → Set l
⟨ A ⟩[ x ≡ y ] = R A x y

-- Total setoids morphisms.
record MapT {l : level} (A : Setoid {l}) (B : Setoid {l}) : Set l where
  field
    appT : el A → el B
    extT : ∀ {x y} → ⟨ A ⟩[ x ≡ y ] → ⟨ B ⟩[ appT x ≡ appT y ]

-- Subsetoids.
