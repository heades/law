-------------------------------------------------------------------------
-- The contents of this file is based on the work in "Setoids in Type  --
-- Theory" by Barthe et. al.                                           --
-- See http://www.cs.ru.nl/~venanzio/publications/Setoids_JFP_2003.pdf --
-------------------------------------------------------------------------
module Setoid.Total where

open import level
open import Relation

open ParRel
open EqRel

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
record Map {l : level} (A : Setoid {l}) (B : Setoid {l}) : Set l where
  field
    appT : el A → el B
    extT : ∀ {x y} → ⟨ A ⟩[ x ≡ y ] → ⟨ B ⟩[ appT x ≡ appT y ]

-- Setoid predicates.
record Pred {l : level} (A : Setoid {l}) : Set (lsuc l) where
  field 
    -- The predicate.
    pf  : el A → Set l
    -- The proof that predicate respects equality.
    inv : ∀{x y} → ⟨ A ⟩[ x ≡ y ] → pf x → pf y   

open Pred

-- Setoid Subcarriers.
record Subcarrier {l : level} (A : Setoid {l}) (P : Pred A) : Set l where 
  field
    subel : el A
    insub : pf P subel

open Subcarrier

-- Subsetoids.
Subsetoid : {l : level} → (A : Setoid {l}) → (P : Pred A) → Setoid {l}
Subsetoid A P with parEqPf (eqRpf A) 
... | a = record { el    = Subcarrier A P; R = λ x y → ⟨ A ⟩[ subel x ≡ subel y ]; 
                   eqRpf = record { parEqPf = record { symPf   = λ x₁ → symPf a x₁; 
                                                       transPf = λ x₁ x₂ → transPf a x₁ x₂ }; 
                                      refPf = λ {x} → refPf (eqRpf A) } }

