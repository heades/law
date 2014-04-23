module Relation where

open import Level renaming (suc to lsuc)
open import Data.Product

-- Partial equivalence relations.
record ParRel {l : Level}{A : Set l}(R : A → A → Set l) : Set l where
  field
    symPf   : ∀{x y} → R x y → R y x
    transPf : ∀{x y z} → R x y → R y z → R x z

-- (Total) equivalence relation. 
record EqRel {l : Level}{A : Set l}(R : A → A → Set l) : Set l where
  field
    parEqPf : ParRel R
    refPf   : ∀{x} → R x x

open ParRel
open EqRel

-- The product of two relations.
ProductRel : {l l' : Level}{A : Set l}{B : Set l'} 
  → (R : A → A → Set l) 
  → (R' : B → B → Set l') 
  → (A × B → A × B → Set (l ⊔ l'))
ProductRel R R' a b = (R (proj₁ a) (proj₁ b)) × (R' (proj₂ a) (proj₂ b))

-- The product of two partial equivalence relations is also a partial
-- equivalence relation.
ProductRelIsParRel : {l l' : Level}{A : Set l}{B : Set l'} 
  → (R : A → A → Set l) 
  → (R' : B → B → Set l') 
  → ParRel R
  → ParRel R'
  → ParRel (ProductRel R R')
ProductRelIsParRel R R' erPF₁ erPF₂ = 
  record { symPf   = λ x₁ → symPf erPF₁ (proj₁ x₁) , symPf erPF₂ (proj₂ x₁); 
           transPf = λ x₁ x₂ → (transPf erPF₁ (proj₁ x₁) (proj₁ x₂)) , (transPf erPF₂ (proj₂ x₁) (proj₂ x₂)) }

-- The product of two (total) equivalence relations is also a (total)
-- equivalence relation.
ProductRelIsEqRel : {l l' : Level}{A : Set l}{B : Set l'} 
  → (R : A → A → Set l) 
  → (R' : B → B → Set l') 
  → EqRel R
  → EqRel R'
  → EqRel (ProductRel R R')
ProductRelIsEqRel R R' erPF₁ erPF₂ = 
  record { parEqPf = ProductRelIsParRel R R' (parEqPf erPF₁) (parEqPf erPF₂); 
           refPf   = λ {x} → (refPf erPF₁ {proj₁ x}) , (refPf erPF₂ {proj₂ x}) }
