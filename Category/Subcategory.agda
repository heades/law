---------------------------------------------------------------
-- This file contains the definitions of several versions of --
-- subcategories.                                            --
---------------------------------------------------------------
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
open Cat

-- Categorical Predicate: A predicate on objects, and morphisms such
-- that the latter is closed under identities and composition.
record CatPred {l : Level} (ℂ : Cat {l}) : Set (lsuc l) where
  field
      oinc : Obj ℂ → Set l
      minc : ∀{A B} → oinc A → oinc B → Pred {l} (Hom ℂ A B)
      cp-idPf : ∀{A} → {p : oinc A} → pf (minc p p) (id ℂ {A})
      cp-compPf : ∀{A B C} → (op₁ : (oinc A))
                        → (op₂ : (oinc B))
                        → (op₃ : (oinc C))
                        → {f : el (Hom ℂ A B)}
                        → {g : el (Hom ℂ B C)} 
                        → (pf (minc op₁ op₂) f)
                        → (pf (minc op₂ op₃) g)
                        → (pf (minc op₁ op₃) (f ○[ comp ℂ ] g))
open CatPred

-- Subcategories:

-- The restriction of a category ℂ to the category determined by the
-- categorical predicate P.  Note that the objects of this category
-- are pairs of an object and a proof that the object belongs in the
-- category, and morphisms are similarly defined but using setoid
-- predicates.
subcatPred : {l : Level}{ℂ : Cat {l}}
  → (P : CatPred ℂ)
  → Cat {l}
subcatPred {_}{ℂ} P = 
  record
    { Obj = Σ[ x ∈ Obj ℂ ]( oinc P x)
    ; Hom = λ AP BP → let A = proj₁ AP
                          B = proj₁ BP 
                          op₁ = proj₂ AP
                          op₂ = proj₂ BP
                      in Subsetoid (Hom ℂ A B) (minc P op₁ op₂)
    ; comp = λ {AP}{BP}{CP} → 
             let A = proj₁ AP
                 B = proj₁ BP 
                 C = proj₁ CP 
                 op₁ = proj₂ AP
                 op₂ = proj₂ BP
                 op₃ = proj₂ CP
             in record { 
                  appT = λ x → 
                           record { 
                             appT = λ x₁ → 
                                      record { subel = (subel x) ○[ comp ℂ ] (subel x₁) ; 
                                               insub = cp-compPf P op₁ op₂ op₃ (insub x) (insub x₁) } ; 
                             extT = λ {y} {z} x₂ → eq-comp-right {_}{ℂ}{A}{B}{C}{subel x}{subel y}{subel z} x₂ } ; 
                  extT = λ {f₁}{f₂} pf g₂ → extT (comp ℂ) pf (subel g₂) }
    ; id = λ {AP} → let A = proj₁ AP 
                        A-op = proj₂ AP 
                    in record { subel = id ℂ ; insub = cp-idPf P {_}{A-op} }
    ; assocPf = assocPf ℂ
    ; idPfCom = idPfCom ℂ
    ; idPf = idPf ℂ
    }

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
    idPf = idPf ℂ;
    idPfCom = idPfCom ℂ
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
     idPf = idPf ℂ;
     idPfCom = idPfCom ℂ}
