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
   eq  : el → el → Set l
   eqRpf : EqRel eq

open Setoid

-- Notation for the underlying equivalence of a setoid.
⟨_⟩[_≡_] : {l : level} → (A : Setoid {l}) → el A → el A → Set l
⟨ A ⟩[ x ≡ y ] = eq A x y

-- Total setoids maps.
record MapTy {l : level} (A : Setoid {l}) (B : Setoid {l}) : Set l where
  field
    appT : el A → el B
    extT : ∀ {x y} → ⟨ A ⟩[ x ≡ y ] → ⟨ B ⟩[ appT x ≡ appT y ]

open MapTy

-- The setoid function space from A to B.
Map : {l : level} → Setoid {l} → Setoid {l} → Setoid {l}
Map A B with parEqPf (eqRpf B)    
... | b = record { el = MapTy A B; 
                   eq = λ f g → ∀ (x : el A) → ⟨ B ⟩[ appT f x ≡ appT g x ]; 
                eqRpf = record { parEqPf = record { symPf = λ x₁ x₂ → symPf b (x₁ x₂); 
                                                  transPf = λ x₁ x₂ x₃ → transPf b (x₁ x₃) (x₂ x₃) }; 
                                 refPf   = λ x₁ → refPf (eqRpf B) } }

-- Total binary setoid maps.
BMap : {l : level} → Setoid {l} → Setoid {l} → Setoid {l} → Set l
BMap A B C = MapTy A (Map B C)

-- A nice notation for composition of BMap's.
_○[_]_ : {l : level}{A B C : Setoid {l}} → el A → BMap A B C → el B → el C
f ○[ comp ] g = appT (appT comp f) g

-- Setoid predicates.
record Pred {l : level} (A : Setoid {l}) : Set (lsuc l) where
  field 
    -- The predicate.
    pf  : el A → Set l
    -- The proof that the predicate respects equality.
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
... | a = record { el    = Subcarrier A P; eq = λ x y → ⟨ A ⟩[ subel x ≡ subel y ]; 
                   eqRpf = record { parEqPf = record { symPf   = λ x₁ → symPf a x₁; 
                                                       transPf = λ x₁ x₂ → transPf a x₁ x₂ }; 
                                      refPf = λ {x} → refPf (eqRpf A) } }
