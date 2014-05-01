module Category.Diagram where

open import Level renaming (suc to lsuc)

open import Equality.Eq
open import Setoid.Total
open import Category.Category
open import Category.Funct
open import Category.Preorder

-- Diagrams are functors from an index category J to a category ℂ.  We
-- think of J as the scheme of the diagram in ℂ.
record Diagram {l₁ l₂ : Level} (J : Cat {l₁}) (ℂ : Cat {l₂}) : Set (l₁ ⊔ l₂) where
  field
    diag : Functor J ℂ

-- A commutative diagram is a diagram from a preorder to a category ℂ.
-- The preorder axiom garauntees that any diagram must commute because
-- there is only one composition.  Mixing this with the fact that
-- functors preserve composition implies that there can only be one
-- composition in ℂ.  This definition goes against the references --
-- nLab and Awedoy's book -- that comm. diagrams must be functors from
-- posets.  In fact we can prove that a PO is enough.  See the next
-- module.
record Comm-Diagram {l₁ l₂ : Level} (J : PO {l₁}) (ℂ : Cat {l₂}) : Set (l₁ ⊔ l₂) where
  field
    diag : Diagram (po-cat J) ℂ

open Comm-Diagram

-- The underlying functor of a diagram.
UFunc : {l l' : Level}{J : PO {l}}{ℂ : Cat {l'}} → Comm-Diagram J ℂ → Functor (po-cat J) ℂ
UFunc D = Diagram.diag (diag D)

-- This module shows that comm. squares can be modeled by POs.
module Diagram-Schemes-Need-Not-Be-Posets where
  open 4PO

  record Comm-Square' 
         {l : Level} 
         (ℂ : Cat {l}) 
         (om : 4Obj → Obj ℂ)
         (g : el (Hom ℂ (om i₁) (om i₂)))
         (h : el (Hom ℂ (om i₂) (om i₄))) 
         (j : el (Hom ℂ (om i₁) (om i₃))) 
         (k : el (Hom ℂ (om i₃) (om i₄))) : Set l where
     field
       Sq : {a b : 4Obj {l}} → SetoidFun (4Hom a b) (Hom ℂ (om a) (om b))
  
       sq-max₁ : ⟨ Hom ℂ (om i₁) (om i₂) ⟩[ appT Sq f₁ ≡ g ]
       sq-max₂ : ⟨ Hom ℂ (om i₁) (om i₃) ⟩[ appT Sq f₂ ≡ j ]
       sq-max₃ : ⟨ Hom ℂ (om i₂) (om i₄) ⟩[ appT Sq f₃ ≡ h ]
       sq-max₄ : ⟨ Hom ℂ (om i₃) (om i₄) ⟩[ appT Sq f₄ ≡ k ]

       sq-funct-id : {i : 4Obj} → ⟨ Hom ℂ (om i) (om i) ⟩[ appT Sq (4Id {_}{i}) ≡ id ℂ ]

       sq-funct-comp : ∀{i j k : 4Obj {l}}{a : el (4Hom i j)}{b : el (4Hom j k)} 
         → ⟨ Hom ℂ (om i) (om k) ⟩[ appT Sq (a ○[ 4Comp {l}{i}{j}{k} ] b) ≡ (appT Sq a) ○[ comp ℂ ] (appT Sq b) ]

  open Comm-Square'

  -- A default function from the objects of the 4PO to the objects of
  -- a square in ℂ.
  sq-default-om : {l : Level}{ℂ : Cat {l}} 
    → Obj ℂ 
    → Obj ℂ 
    → Obj ℂ 
    → Obj ℂ 
    → (4Obj {l} → Obj ℂ)
  sq-default-om A B D C i₁ = A
  sq-default-om A B D C i₂ = B
  sq-default-om A B D C i₃ = D
  sq-default-om A B D C i₄ = C

  -- Commutative squares in ℂ.
  Comm-Square : {l : Level}{ℂ : Cat {l}} 
    → (A B D C : Obj ℂ) 
    → (g : el (Hom ℂ A B)) 
    → (h : el (Hom ℂ B C)) 
    → (j : el (Hom ℂ A D)) 
    → (k : el (Hom ℂ D C)) 
    → Set l
  Comm-Square {_} {ℂ} A B D C g h j k = Comm-Square' ℂ (sq-default-om {_} {ℂ} A B D C) g h j k

  -- Commutative squares are functors.
  Comm-Square-is-Functor : ∀{l}{ℂ : Cat {l}}{A B D C}
    → {g : el (Hom ℂ A B)}
    → {h : el (Hom ℂ B C)}
    → {j : el (Hom ℂ A D)}
    → {k : el (Hom ℂ D C)}
    → Comm-Square {_} {ℂ} A B D C g h j k
    → Functor {l} 4cat ℂ
  Comm-Square-is-Functor {_} {ℂ} {A} {B} {D} {C} {g} {h} {j} {k} sq = 
    record { omap = sq-default-om {_}{ℂ} A B D C; 
             fmap = λ {A₁} {B₁} → Sq sq {A₁} {B₁}; 
             idPF = sq-funct-id sq; 
           compPF = λ {A₁} {B₁} {C₁} {f} {g₁} → sq-funct-comp sq {A₁}{B₁}{C₁}{f}{g₁} }

  -- The former now implies that we have a commutative diagram.
  Comm-Square-is-Comm-Diagram : ∀{l}{ℂ : Cat {l}}{A B D C}
    → {g : el (Hom ℂ A B)}
    → {h : el (Hom ℂ B C)}
    → {j : el (Hom ℂ A D)}
    → {k : el (Hom ℂ D C)}
    → Comm-Square {_} {ℂ} A B D C g h j k
    → Comm-Diagram {l}{l} 4po ℂ
  Comm-Square-is-Comm-Diagram {l}{ℂ}{g}{h}{j}{k} sq = 
    record { diag = record { diag = Comm-Square-is-Functor sq } }

  -- If we have a commutative square, then it commutes in ℂ.
  Comm-Square-Commutes : ∀{l}{ℂ : Cat {l}}{A B D C}
    → {g : el (Hom ℂ A B)}
    → {h : el (Hom ℂ B C)}
    → {j : el (Hom ℂ A D)}
    → {k : el (Hom ℂ D C)}
    → Comm-Square {_} {ℂ} A B D C g h j k
    → ⟨ Hom ℂ A C ⟩[ g ○[ comp ℂ ] h ≡ j ○[ comp ℂ ] k ]
  Comm-Square-Commutes {l}{ℂ}{A}{B}{D}{C}{g}{h}{j}{k} sq with sq-funct-comp sq {i₁}{i₂}{i₄}{f₁}{f₃} | sq-funct-comp sq {i₁}{i₃}{i₄}{f₂}{f₄}
  ... | sq-eq₁ | sq-eq₂ with transPf (parEqPf (eqRpf (Hom ℂ A C))) (symPf (parEqPf (eqRpf (Hom ℂ A C))) sq-eq₁) sq-eq₂
  ... | sq-eq₃ with eq-comp-all {_}{ℂ}{A}{B}{C}{g}
                                {appT {_}{_}{4Hom i₁ i₂} {Hom ℂ A B} (Sq sq {i₁}{i₂}) f₁}
                                {h}
                                {appT (Sq sq {i₂}{i₄}) f₃} 
                                (symPf (parEqPf (eqRpf (Hom ℂ A B))) (sq-max₁ sq)) 
                                (symPf (parEqPf (eqRpf (Hom ℂ B C))) (sq-max₃ sq))
  ... | sq-eq₄ with eq-comp-all {_}{ℂ}{A}{D}{C}
                                {appT {_}{_}{4Hom i₁ i₃} {Hom ℂ A D} (Sq sq {i₁}{i₃}) f₂}
                                {j}                              
                                {appT (Sq sq {i₃}{i₄}) f₄} 
                                {k}                              
                                (sq-max₂ sq)
                                (sq-max₄ sq)
  ... | sq-eq₅ with transPf (parEqPf (eqRpf (Hom ℂ A C))) sq-eq₄ sq-eq₃
  ... | sq-eq₆ = transPf (parEqPf (eqRpf (Hom ℂ A C))) sq-eq₆ sq-eq₅
