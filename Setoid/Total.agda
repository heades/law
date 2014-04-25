----------------------------------------------------------------------------------
-- The contents of this file is based on the work in "Setoids in Type           --
-- Theory" by Barthe et al. and Capretta's "Universal Algebra in Type Theory."  --
--                                                                              --
-- See http://www.cs.ru.nl/~venanzio/publications/Setoids_JFP_2003.pdf and      --
-- http://www.cs.ru.nl/~venanzio/publications/Universal_Algebra_TPHOLs_1999.pdf --
----------------------------------------------------------------------------------
module Setoid.Total where

open import Level renaming (suc to lsuc)
open import Data.Product

open import Relation.Relation

open ParRel
open EqRel

-- Total setoids.
record Setoid {l : Level} : Set (lsuc l) where
 field 
   el : Set l
   eq  : el → el → Set l
   eqRpf : EqRel eq

open Setoid public

-- Notation for the underlying equivalence of a setoid.
⟨_⟩[_≡_] : {l : Level} → (A : Setoid {l}) → el A → el A → Set l
⟨ A ⟩[ x ≡ y ] = eq A x y

-- Total setoids maps.  Barthe et al. calls "map."
record SetoidFun {l₁ l₂ : Level} (A : Setoid {l₁}) (B : Setoid {l₂}) : Set (l₁ ⊔ l₂) where
  field
    appT : el A → el B
    extT : ∀ {x y} → ⟨ A ⟩[ x ≡ y ] → ⟨ B ⟩[ appT x ≡ appT y ]

open SetoidFun public

-- The setoid function space from A to B.  Barthe et al. calls this
-- "Map."
SetoidFunSpace : {l₁ l₂ : Level} → Setoid {l₁} → Setoid {l₂} → Setoid {l₁ ⊔ l₂}
SetoidFunSpace A B with parEqPf (eqRpf B)    
... | b = record { el = SetoidFun A B; 
                   eq = λ f g → ∀ (x : el A) → ⟨ B ⟩[ appT f x ≡ appT g x ]; 
                eqRpf = record { parEqPf = record { symPf = λ x₁ x₂ → symPf b (x₁ x₂); 
                                                  transPf = λ x₁ x₂ x₃ → transPf b (x₁ x₃) (x₂ x₃) }; 
                                 refPf   = λ x₁ → refPf (eqRpf B) } }

-- Total binary setoid maps.
BinSetoidFun : {l₁ l₂ l₃ : Level} → Setoid {l₁} → Setoid {l₂} → Setoid {l₃} → Set (l₁ ⊔ l₂ ⊔ l₃)
BinSetoidFun A B C = SetoidFun A (SetoidFunSpace B C)

-- A nice notation for composition of BMap's.
_○[_]_ : {l : Level}{A B C : Setoid {l}} → el A → BinSetoidFun A B C → el B → el C
f ○[ comp ] g = appT (appT comp f) g

-- Setoid predicates.
record Pred {l : Level} (A : Setoid {l}) : Set (lsuc l) where
  field 
    -- The predicate.
    pf  : el A → Set l
    -- The proof that the predicate respects equality.
    inv : ∀{x y} → ⟨ A ⟩[ x ≡ y ] → pf x → pf y   

open Pred

-- Setoid Subcarriers.
record Subcarrier {l : Level} (A : Setoid {l}) (P : Pred A) : Set l where 
  field
    subel : el A
    insub : pf P subel

open Subcarrier

-- Subsetoids.
Subsetoid : {l : Level} → (A : Setoid {l}) → (P : Pred A) → Setoid {l}
Subsetoid A P with parEqPf (eqRpf A) 
... | a = record { el    = Subcarrier A P; eq = λ x y → ⟨ A ⟩[ subel x ≡ subel y ]; 
                   eqRpf = record { parEqPf = record { symPf   = λ x₁ → symPf a x₁; 
                                                       transPf = λ x₁ x₂ → transPf a x₁ x₂ }; 
                                    refPf = λ {x} → refPf (eqRpf A) } }

-- The product of two setoids.
ProductSetoid : {l₁ l₂ : Level} → Setoid {l₁} → Setoid {l₂} → Setoid {l₁ ⊔ l₂}
ProductSetoid A B =  record { el = (el A) × (el B); 
                              eq = ProductRel (eq A) (eq B); 
                           eqRpf = ProductRelIsEqRel (eq A) (eq B) (eqRpf A) (eqRpf B) }
_●ₛ_ : {l₁ l₂ : Level} → Setoid {l₁} → Setoid {l₂} → Setoid {l₁ ⊔ l₂}
A ●ₛ B = ProductSetoid A B

-- Product setoid functions.
ProdSetoidFun : {l₁ l₂ l₃ l₄ : Level}
                {A₁ : Setoid {l₁}}
                {B₁ : Setoid {l₂}}
                {A₂ : Setoid {l₃}}
                {B₂ : Setoid {l₄}}
              → (F₁ : SetoidFun A₁ A₂)
              → (F₂ : SetoidFun B₁ B₂)
              → SetoidFun (A₁ ●ₛ B₁) (A₂ ●ₛ B₂)
ProdSetoidFun F₁ F₂ = record { appT = λ x → appT F₁ (proj₁ x) , appT F₂ (proj₂ x); 
                               extT = λ x₁ → extT F₁ (proj₁ x₁) , extT F₂ (proj₂ x₁) }

-- Binary product setoid functions.
BinProdSetoidFun : {l₁ l₂ l₃ l₄ : Level}
                   {A₁ : Setoid {l₁}}
                   {B₁ : Setoid {l₂}}
                   {C₁ : Setoid {l₃}}
                   {A₂ : Setoid {l₄}}
                   {B₂ : Setoid {l₄}}
                   {C₂ : Setoid {l₄}}
                 → (F₁ : BinSetoidFun A₁ B₁ C₁)
                 → (F₂ : BinSetoidFun A₂ B₂ C₂)
                 → BinSetoidFun (A₁ ●ₛ A₂) (B₁ ●ₛ B₂) (C₁ ●ₛ C₂)
BinProdSetoidFun F₁ F₂ = record { appT = λ x → ProdSetoidFun (appT F₁ (proj₁ x)) (appT F₂ (proj₂ x));
                                  extT = λ {a b} c d → (extT F₁ (proj₁ c) (proj₁ d)) , (extT F₂ (proj₂ c) (proj₂ d)) }

_●b_ : {l₁ l₂ l₃ l₄ : Level}
                   {A₁ : Setoid {l₁}}
                   {B₁ : Setoid {l₂}}
                   {C₁ : Setoid {l₃}}
                   {A₂ : Setoid {l₄}}
                   {B₂ : Setoid {l₄}}
                   {C₂ : Setoid {l₄}}
                 → (F₁ : BinSetoidFun A₁ B₁ C₁)
                 → (F₂ : BinSetoidFun A₂ B₂ C₂)
                 → BinSetoidFun (A₁ ●ₛ A₂) (B₁ ●ₛ B₂) (C₁ ●ₛ C₂)
F₁ ●b F₂ = BinProdSetoidFun F₁ F₂

-- Next we define a relaxed notion of a subsetoid where the predicate
-- does not have to be invariant on the equality.
↓Setoid : {l : Level} 
  → (S : Setoid {l}) 
  → (P : el S → Set l)
  → Setoid {l}
↓Setoid S P = 
  record { el = eq S ↓ P; 
           eq = λ f g → ⟨ S ⟩[ proj₁ f ≡ proj₁ g ]; 
        eqRpf = ↓EqRel (eq S) P (eqRpf S)}

-- Restricted setoid functions.
↓SetoidFun : 
    {l : Level}
    {S₁ S₂ : Setoid {l}}
    {P₁ : el S₁ → Set l}
    {P₂ : el S₂ → Set l}
  → (F : SetoidFun S₁ S₂)
  → ({f : el S₁} → (P₁ f) → P₂ (appT F f))
  → SetoidFun (↓Setoid S₁ P₁) (↓Setoid S₂ P₂)
↓SetoidFun {l}{S₁}{S₂}{P₁}{P₂} F pf = 
  record { appT = λ x₁ → appT F (proj₁ x₁) , pf {proj₁ x₁} (proj₂ x₁); 
           extT = λ {x}{y} x₂ → extT F x₂ }

-- Binary restricted setoid functions.
↓BinSetoidFun : 
    {l : Level}
    {S₁ S₂ S₃ : Setoid {l}}
    {P₁ : el S₁ → Set l}
    {P₂ : el S₂ → Set l}
    {P₃ : el S₃ → Set l}
  → (F : BinSetoidFun S₁ S₂ S₃)
  → ({f : el S₁}{g : el S₂} → (P₁ f) → (P₂ g) → P₃ (f ○[ F ] g))
  → BinSetoidFun (↓Setoid S₁ P₁) (↓Setoid S₂ P₂) (↓Setoid S₃ P₃)
↓BinSetoidFun {l}{S₁}{S₂}{S₃}{P₁}{P₂}{P₃} F pf = 
  record { appT = λ f → ↓SetoidFun (appT F (proj₁ f)) (pf (proj₂ f)); 
           extT = λ x₁ x₂ → extT F x₁ (proj₁ x₂) }
