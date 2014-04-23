module Category where

open import Level renaming (suc to lsuc)
open import Data.Product

open import Setoid.Total
open import Relation

open Setoid
open SetoidFun
open Pred
open Subcarrier
open EqRel

-- The definition of categories.
record Cat {l : Level} : Set (lsuc l) where
  field
    Obj     : Set l
    Hom     : Obj → Obj → Setoid {l}
    comp    : {A B C : Obj} → BinSetoidFun (Hom A B) (Hom B C) (Hom A C)
    id      : {A : Obj} → el (Hom A A) 
    assocPf : ∀{A B C D}{f : el (Hom A B)}{g : el (Hom B C)}{h : el (Hom C D)} 
               → ⟨ Hom A D ⟩[ f ○[ comp ] (g ○[ comp ] h)  ≡  (f ○[ comp ] g) ○[ comp ] h ]
    idPf    : ∀{A B}{f : el (Hom A B)} → ⟨ Hom A B ⟩[ id ○[ comp ] f ≡ f ○[ comp ] id  ]

open Cat

-- Subcategories.
strict-replete-subcat : {l : Level} → (ℂ : Cat {l})(O : Set l) 
  → (oinc : O → Obj ℂ) 
  → (minc : ∀{A B} → Pred {l} (Hom ℂ (oinc A) (oinc B)))
  → (∀{A} → pf (minc {A}{A}) (id ℂ {oinc A}))
  → (∀{A B C}
         → {f : el (Hom ℂ (oinc A) (oinc B))}
         → {g : el (Hom ℂ (oinc B) (oinc C))} 
         → (pf minc f)
         → (pf minc g) 
         → (pf minc (f ○[ comp ℂ ] g)))
  → Cat {l}
strict-replete-subcat ℂ O oinc minc idPF compPF = 
  record {
    Obj = O;
    Hom = λ A B → Subsetoid (Hom ℂ (oinc A) (oinc B)) (minc {A}{B});                                     
    comp = λ {A} {B} {C} → 
      record { appT = λ x → 
                record { appT = λ x₁ → 
                              record { subel = (subel x) ○[ comp ℂ ] (subel x₁); 
                                       insub = compPF {f = subel x}{subel x₁} (insub x) (insub x₁) }; 
                         extT =  λ {y}{z} p → extT (appT (comp ℂ {oinc A}{oinc B}{oinc C}) (subel x)) {subel y}{subel z} p }; 
               extT = λ {y}{z} x₁ x₂ → extT (comp ℂ {oinc A} {oinc B} {oinc C}) x₁ (subel x₂) };
    id = λ {A} → record { subel = id ℂ {oinc A}; insub = idPF {A} };
    assocPf = assocPf ℂ;
    idPf = idPf ℂ 
  }

