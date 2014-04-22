module Category where

open import level

open import Setoid.Total

open Setoid
open MapTy

-- The definition of categories.
record Cat {l : level} : Set (lsuc l) where
  field
    Obj     : Set l
    Hom     : Obj → Obj → Setoid {l}
    comp    : {A B C : Obj} → BMap (Hom A B) (Hom B C) (Hom A C)
    id      : {A : Obj} → el (Hom A A) 
    assocPf : ∀{A B C D}{f : el (Hom A B)}{g : el (Hom B C)}{h : el (Hom C D)} 
               → ⟨ Hom A D ⟩[ f ○[ comp ] (g ○[ comp ] h)  ≡  (f ○[ comp ] g) ○[ comp ] h ]
    idPf    : ∀{A B}{f : el (Hom A B)} → ⟨ Hom A B ⟩[ id ○[ comp ] f ≡ f ○[ comp ] id  ]
