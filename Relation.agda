module Relation where

open import level

-- Partial equivalence relations.
record ParRel {l : level}{A : Set l}(R : A → A → Set l) : Set l where
  field
    symPf   : ∀{x y} → R x y → R y x
    transPf : ∀{x y z} → R x y → R y z → R x z

-- (Total) equivalence relation. 
record EqRel {l : level}{A : Set l}(R : A → A → Set l) : Set l where
  field
    parEqPf : ParRel R
    refPf   : ∀{x} → R x x

