----------------------------------------------------------------
-- This file contains the definition of categories.           --
----------------------------------------------------------------
module Category.Category where

open import Level public renaming (suc to lsuc)
open import Data.Product

open import Setoid.Total public
open import Relation.Relation

open Setoid public

record Cat {l : Level} : Set (lsuc l) where
  field
    Obj     : Set l
    Hom     : Obj → Obj → Setoid {l}
    comp    : {A B C : Obj} → BinSetoidFun (Hom A B) (Hom B C) (Hom A C)
    id      : {A : Obj} → el (Hom A A) 
    assocPf : ∀{A B C D}{f : el (Hom A B)}{g : el (Hom B C)}{h : el (Hom C D)} 
               → ⟨ Hom A D ⟩[ f ○[ comp ] (g ○[ comp ] h)  ≡  (f ○[ comp ] g) ○[ comp ] h ]
    idPfCom : ∀{A B}{f : el (Hom A B)} → ⟨ Hom A B ⟩[ id ○[ comp ] f ≡ f ○[ comp ] id  ]
    idPf    : ∀{A B}{f : el (Hom A B)} → ⟨ Hom A B ⟩[ id ○[ comp ] f ≡ f ]

open Cat public

-- Identities composed on the left cancel.
idPf-left : ∀{l}{ℂ : Cat {l}}{A B : Obj ℂ}{f : el (Hom ℂ A B)} → ⟨ Hom ℂ A B ⟩[ f ○[ comp ℂ ] id ℂ ≡ f ]
idPf-left {_}{ℂ}{A}{B}{f} = 
  transPf (parEqPf (eqRpf (Hom ℂ A B)))
          (symPf (parEqPf (eqRpf (Hom ℂ A B))) (idPfCom ℂ {A} {B} {f})) 
          (idPf ℂ)

-- Congruence results for composition.
eq-comp-right : ∀{l}
    {ℂ : Cat {l}}
    {A B C : Obj ℂ}
    {f : el (Hom ℂ A B)}
    {g₁ g₂ : el (Hom ℂ B C)} 
  → ⟨ Hom ℂ B C ⟩[ g₁ ≡ g₂ ] 
  → ⟨ Hom ℂ A C ⟩[ f ○[ comp ℂ ] g₁ ≡ f ○[ comp ℂ ] g₂ ]
eq-comp-right {_}{ℂ}{A}{B}{C}{f}{g₁}{g₂} eq = 
  extT (appT {_}{_}{Hom ℂ A B}{SetoidFunSpace (Hom ℂ B C) (Hom ℂ A C)} (comp ℂ) f) eq

eq-comp-left : ∀{l}
    {ℂ : Cat {l}}
    {A B C : Obj ℂ}
    {f₁ f₂ : el (Hom ℂ A B)}
    {g : el (Hom ℂ B C)} 
  → ⟨ Hom ℂ A B ⟩[ f₁ ≡ f₂ ] 
  → ⟨ Hom ℂ A C ⟩[ f₁ ○[ comp ℂ ] g ≡ f₂ ○[ comp ℂ ] g ]
eq-comp-left {_}{ℂ}{A}{B}{C}{f₁}{f₂}{g} eq = extT (comp ℂ) {f₁}{f₂} eq g

eq-comp-all : ∀{l}
    {ℂ : Cat {l}}
    {A B C : Obj ℂ}
    {f₁ f₂ : el (Hom ℂ A B)}
    {g₁ g₂ : el (Hom ℂ B C)} 
  → ⟨ Hom ℂ A B ⟩[ f₁ ≡ f₂ ] 
  → ⟨ Hom ℂ B C ⟩[ g₁ ≡ g₂ ]
  → ⟨ Hom ℂ A C ⟩[ f₁ ○[ comp ℂ ] g₁ ≡ f₂ ○[ comp ℂ ] g₂ ]
eq-comp-all {_}{ℂ}{A}{B}{C}{f₁}{f₂}{g₁}{g₂} eq₁ eq₂ 
  with eq-comp-left {_}{ℂ}{A}{B}{C}{f₁}{f₂}{g₁} eq₁ | 
       eq-comp-right {_}{ℂ}{A}{B}{C}{f₂}{g₁}{g₂} eq₂
... | eq₃ | eq₄ = transPf (parEqPf (eqRpf (Hom ℂ A C))) eq₃ eq₄
