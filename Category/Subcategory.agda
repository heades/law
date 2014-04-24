module Category.Subcategory where

open import Level
open import Data.Product

open import Setoid.Total
open import Relation.Relation
open import Category.Category

open Setoid
open SetoidFun
open Pred
open Subcarrier
open EqRel

-- Subcategories using subsetoids.
subcat : {l : Level} 
  → (ℂ : Cat {l})(O : Set l) 
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
subcat ℂ O oinc minc idPF compPF = 
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

-- An alternate definition of a subcategory where the predicate is not
-- a setoid predicate.
subcat-pred : {l : Level} 
  → (ℂ : Cat {l})(O : Set l) 
  → (oinc : O → Obj ℂ) 
  → (minc : ∀{A B} → el (Hom ℂ (oinc A) (oinc B)) → Set l)
  → (∀{A} → minc (id ℂ {oinc A}))
  → (∀{A B C}
         → {f : el (Hom ℂ (oinc A) (oinc B))}
         → {g : el (Hom ℂ (oinc B) (oinc C))} 
         → (minc f)
         → (minc g) 
         → (minc (f ○[ comp ℂ ] g)))
  → Cat {l}
subcat-pred ℂ O oinc minc idPF compPF =   
    record {                
      Obj = O;
      Hom = λ A B → ↓Setoid (Hom ℂ (oinc A) (oinc B)) (minc {A}{B});
     comp = λ {A} {B} {C} → ↓BinSetoidFun (comp ℂ) compPF;
       id = (id ℂ , idPF);
  assocPf = assocPf ℂ;
     idPf = idPf ℂ }
