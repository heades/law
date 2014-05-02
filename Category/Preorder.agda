------------------------------------------------------------------------
-- This file contains the definition of a preorder as a category with --
-- additional properties.                                             --
------------------------------------------------------------------------
module Category.Preorder where

open import Level renaming (suc to lsuc)
open import Data.Empty

open import Setoid.Total
open import Category.Category
open import Equality.Eq

record PO {l : Level} : Set (lsuc l) where
  field
    -- The underlying category.
    ℙ : Cat {l}

    -- The preorder axiom.
    POax : ∀{A B}{f g : el (Hom ℙ A B)} → ⟨ Hom ℙ A B ⟩[ f ≡ g ]

open PO public renaming (ℙ to po-cat)

-- A PO with 4 objects.
module 4PO where
    -- The objects.
    data 4Obj {l : Level} : Set l where
      i₁ : 4Obj
      i₂ : 4Obj
      i₃ : 4Obj
      i₄ : 4Obj

    -- The PreHom.
    data 4PHom {l : Level} : 4Obj {l} → 4Obj {l} → Set l where
      id₁ : 4PHom i₁ i₁
      f₁ : 4PHom i₁ i₂      
      f₂ : 4PHom i₁ i₃      
      id₂ : 4PHom i₂ i₂
      f₃ : 4PHom i₂ i₄            
      id₃ : 4PHom i₃ i₃      
      f₄ : 4PHom i₃ i₄            
      f₅ : 4PHom i₁ i₄
      id₄ : 4PHom i₄ i₄   
    
    -- The Hom.
    4Hom : {l : Level} → 4Obj {l} → 4Obj {l} → Setoid {l}
    4Hom i₁ i₁ = record { el = 4PHom i₁ i₁; eq = λ a b → a ≅ b; eqRpf = isEqRel }
    4Hom i₁ i₂ = record { el = 4PHom i₁ i₂; eq = λ a b → a ≅ b; eqRpf = isEqRel }
    4Hom i₁ i₃ = record { el = 4PHom i₁ i₃; eq = λ a b → a ≅ b; eqRpf = isEqRel }
    4Hom i₁ i₄ = record { el = 4PHom i₁ i₄; eq = λ a b → a ≅ b; eqRpf = isEqRel }    
    4Hom i₂ i₂ = record { el = 4PHom i₂ i₂; eq = λ a b → a ≅ b; eqRpf = isEqRel }
    4Hom i₂ i₄ = record { el = 4PHom i₂ i₄; eq = λ a b → a ≅ b; eqRpf = isEqRel }
    4Hom i₃ i₃ = record { el = 4PHom i₃ i₃; eq = λ a b → a ≅ b; eqRpf = isEqRel }
    4Hom i₃ i₄ = record { el = 4PHom i₃ i₄; eq = λ a b → a ≅ b; eqRpf = isEqRel }
    4Hom i₄ i₄ = record { el = 4PHom i₄ i₄; eq = λ a b → a ≅ b; eqRpf = isEqRel }
    4Hom  _  _ = EmptySetoid
    
    4Comp : {l : Level}{a b c : 4Obj {l}} → BinSetoidFun (4Hom a b) (4Hom b c) (4Hom a c)
    4Comp {_} {i₁} {i₂} {i₁} = record { appT = λ x → record { appT = λ x₁ → id₁; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₁} {i₁} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₂} {i₁} {i₂} = record { appT = λ x → record { appT = λ x₁ → id₂; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₁} {i₃} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₂} {i₁} {i₄} = record { appT = λ x → record { appT = λ x₁ → f₃; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₁} {i₁} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₃} {i₂} {i₁} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₁} {i₂} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₃} {i₁} {i₃} = record { appT = λ x → record { appT = λ x₁ → id₃; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₁} {i₄} = record { appT = λ x → record { appT = λ x₁ → f₄; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₄} {i₁} {i₁} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₄} {i₂} {i₁} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₄} {i₁} {i₂} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₄} {i₁} {i₃} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₄} {i₃} {i₃} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₄} {i₁} {i₄} = record { appT = λ x → record { appT = λ x₁ → ⊥-poly-elim x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₄} {i₄} {i₃} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₄} {i₄} {i₂} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₄} {i₄} {i₁} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₄} {i₃} {i₄} = record { appT = λ x → record { appT = λ x₁ → id₄; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₄} {i₃} {i₂} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₄} {i₃} {i₁} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₄} {i₂} {i₄} = record { appT = λ x → record { appT = λ x₁ → id₄; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₄} {i₂} {i₃} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₄} {i₂} {i₂} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₃} {i₄} {i₃} = record { appT = λ x → record { appT = λ x₁ → id₃; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₄} {i₂} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₄} {i₁} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₃} {i₄} = record { appT = λ x → record { appT = λ x₁ → f₄; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₃} {i₂} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₃} {i₁} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₂} {i₄} = record { appT = λ x → record { appT = λ x₁ → f₄; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₂} {i₃} = record { appT = λ x → record { appT = λ x₁ → id₃; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₃} {i₂} {i₂} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₃} {i₄} {i₄} = record { appT = λ x → record { appT = λ x₁ → f₄; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₄} {i₃} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₄} {i₂} = record { appT = λ x → record { appT = λ x₁ → id₂; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₄} {i₁} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₃} {i₄} = record { appT = λ x → record { appT = λ x₁ → f₃; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₃} {i₂} = record { appT = λ x → record { appT = λ x₁ → id₂; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₃} {i₁} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₂} {i₂} {i₄} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₂} {i₃} = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₂} {i₂} = record { appT = λ x → record { appT = λ x₁ → id₂; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₂} {i₃} {i₃} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₂} {i₄} {i₄} = record { appT = λ x → record { appT = λ x₁ → x; extT = λ x₂ → refl }; extT = λ x₁ x₂ → x₁ }
    4Comp {_} {i₁} {i₄} {i₃} = record { appT = λ x → record { appT = λ x₁ → f₂; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₄} {i₂} = record { appT = λ x → record { appT = λ x₁ → f₁; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₄} {i₁} = record { appT = λ x → record { appT = λ x₁ → id₁; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₃} {i₄} = record { appT = λ x → record { appT = λ x₁ → f₅; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₃} {i₂} = record { appT = λ x → record { appT = λ x₁ → f₁; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₃} {i₁} = record { appT = λ x → record { appT = λ x₁ → id₁; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₂} {i₄} = record { appT = λ x → record { appT = λ x₁ → f₅; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₂} {i₃} = record { appT = λ x → record { appT = λ x₁ → f₂; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₂} {i₂} = record { appT = λ x → record { appT = λ x₁ → f₁; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₃} {i₃} = record { appT = λ x → record { appT = λ x₁ → f₂; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {_} {i₁} {i₄} {i₄} = record { appT = λ x → record { appT = λ x₁ → f₅; extT = λ x₂ → refl }; extT = λ x₁ x₂ → refl }
    4Comp {l} {i₁} {i₁} {c}  = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refPf (eqRpf (4Hom i₁ c)) {x₂} }
    4Comp {l} {i₂} {i₂} {c}  = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refPf (eqRpf (4Hom i₂ c)) {x₂} }
    4Comp {l} {i₃} {i₃} {c}  = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refPf (eqRpf (4Hom i₃ c)) {x₂} } 
    4Comp {l} {i₄} {i₄} {c}  = record { appT = λ x → record { appT = λ x₁ → x₁; extT = λ x₂ → x₂ }; extT = λ x₁ x₂ → refPf (eqRpf (4Hom i₄ c)) {x₂} }

    4Id : {l : Level}{A : 4Obj {l}} → el (4Hom A A)
    4Id {_}{i₁} = id₁
    4Id {_}{i₂} = id₂
    4Id {_}{i₃} = id₃
    4Id {_}{i₄} = id₄

    4PO-ax : ∀{l}{A B : 4Obj {l}}{f g : el (4Hom A B)} → eq (4Hom A B) f g
    4PO-ax {A = i₁} {i₁} {id₁} {id₁} = refl
    4PO-ax {A = i₁} {i₂} {f₁}  {f₁}  = refl
    4PO-ax {A = i₁} {i₃} {f₂}  {f₂}  = refl
    4PO-ax {A = i₁} {i₄} {f₅}  {f₅}  = refl
    4PO-ax {A = i₂} {i₂} {id₂} {id₂} = refl
    4PO-ax {A = i₂} {i₄} {f₃}  {f₃}  = refl    
    4PO-ax {A = i₃} {i₃} {id₃} {id₃} = refl
    4PO-ax {A = i₃} {i₄} {f₄}  {f₄}  = refl
    4PO-ax {A = i₄} {i₄} {id₄} {id₄} = refl
    4PO-ax {A = i₂} {i₁} {f}         = ⊥-poly-elim f
    4PO-ax {A = i₃} {i₁} {f}         = ⊥-poly-elim f
    4PO-ax {A = i₄} {i₁} {f}         = ⊥-poly-elim f    
    4PO-ax {A = i₃} {i₂} {f}         = ⊥-poly-elim f
    4PO-ax {A = i₄} {i₂} {f}         = ⊥-poly-elim f
    4PO-ax {A = i₂} {i₃} {f}         = ⊥-poly-elim f    
    4PO-ax {A = i₄} {i₃} {f}         = ⊥-poly-elim f

    4AssocPf : ∀{l}{A B C D : 4Obj {l}} {f : el (4Hom A B)} {g : el (4Hom B C)}{h : el (4Hom C D)} 
      → ⟨ 4Hom A D ⟩[ f ○[ 4Comp {l} {A}{B}{D} ] (g ○[ 4Comp {l}{B}{C}{D} ] h) ≡ (f ○[ 4Comp {l} {A}{B}{C} ] g) ○[ 4Comp {l}{A}{C}{D} ] h ]
    4AssocPf {l}{A}{B}{C}{D} {f}{g} = 4PO-ax {l} {A} {D}
    
    4IdPF : {l : Level}{A B : 4Obj {l}} {f : el (4Hom A B)} 
      → ⟨ 4Hom A B ⟩[ (4Id {l}{A}) ○[ 4Comp {l}{A}{A}{B} ] f ≡ f ○[ 4Comp {l}{A}{B}{B} ] (4Id {l}{B}) ]
    4IdPF {l}{A}{B}{f} = 4PO-ax {l} {A} {B}

    -- We have a category.
    4cat : {l : Level} → Cat {l}
    4cat {l} = record { Obj = 4Obj {l};
                        Hom = 4Hom;
                       comp = λ {A} {B} {C} → 4Comp {l} {A}{B}{C};
                         id = λ {A} → 4Id {l}{A};
                    assocPf = λ {A} {B} {C} {D} {f} {g} {h} → 4AssocPf {l}{A}{B}{C}{D}{f}{g}{h};
                       idPfCom = λ {A} {B} {f} → 4IdPF {l}{A}{B}{f};
                       idPf = λ {A} {B} {f} → 4PO-ax {l} {A} {B}}

    -- We have a preorder.
    4po : {l : Level} → PO {l}
    4po {l} = record { ℙ = 4cat;
                    POax = λ {A} {B} {f} {g} → 4PO-ax {l} {A} {B} {f} {g} }
