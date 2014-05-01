---------------------------------------------------------------------
-- This file contains the definition of heterogenous equality and  --
-- related facts.  A lot of this code is old, and could be written --
-- better.   This equality is mainly used for object equivalence.  --
--                                                                 --
-- Some of it came from the paper:                                 --
--   "Monads Need Not Be Endofunctors" by Altenkirch et al.        --
--                                                                 --
-- See: http://www.cs.nott.ac.uk/~txa/publ/Relative_Monads.pdf     --
---------------------------------------------------------------------

module Equality.Eq where

open import Level

open import Relation.Relation

open import Relation.Binary.PropositionalEquality public renaming (sym to prop-sym ; trans to prop-trans; refl to prop-refl)

data _≅_ {l : Level} {A : Set l} (a : A) : {A' : Set l} → A' → Set l where
  refl : a ≅ a


postulate ext : ∀{i j}{A : Set i}{B B' : A → Set j}{f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a ≅ g a) → f ≅ g

postulate prop-ext : ∀{i j}{A : Set i}{B : A → Set j}{f : ∀ a → B a}{g : ∀ a → B a} → 
                (∀ a → f a ≡ g a) → f ≡ g

≅-to-≡ : ∀{l : Level}{A : Set l}{a b : A} → a ≅ b → a ≡ b
≅-to-≡ refl = prop-refl

-- this could just be derived from ext
postulate iext : ∀{i j}{A : Set i}{B B' : A → Set j}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
                 (∀ a → f {a} ≅ g {a}) → 
                 _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

sym : ∀{l : Level}{A : Set l }{a b : A} → a ≅ b → b ≅ a
sym refl = refl

trans : ∀{l : Level}{A : Set l}{a b c : A} → a ≅ b → b ≅ c → a ≅ c
trans refl refl = refl

isEqRel : ∀{l : Level}{A : Set l} → EqRel {A = A}  (λ x y → x ≅ y)
isEqRel {l} {A} = record { parEqPf = record { symPf = sym; transPf = trans }; refPf = refl }

ir : ∀{l : Level}{A A' : Set l}{a : A}{a' : A'}{p q : a ≅ a'} → p ≅ q
ir {p = refl}{q = refl} = refl

eqApp : ∀{l l' : Level}{A : Set l}{B : Set l'}{f : A → B}{b c : A} → b ≅ c → (f b) ≅ (f c)
eqApp refl = refl

-- Cite from relative monads paper.
deqApp : ∀{l : Level}{A : Set l}{B : A → Set l}(f : ∀ a → B a){a a' : A} 
  → a ≅ a' → f a ≅ f a'
deqApp f refl = refl

feqApp : ∀{l l' : Level}{A : Set l}{B : Set l'}{f f' : A → B}{b c : A} → f ≅ f' → b ≅ c → (f b) ≅ (f' c)
feqApp refl refl = refl

ifeqApp : ∀{i j}{A : Set i}{B : A → Set j}{f f' : {x : A} → B x}(a : A) → _≅_ {_}{ {a : A} → B a} f { {a : A} → B a} f' → f {a} ≅ f' {a}
ifeqApp a refl = refl

ieqApp : ∀{x y}{A : Set x}{B : A → Set y}(f : ∀ {a} → B a){a a' : A} → a ≅ a' → f {a} ≅ f {a'}
ieqApp f refl = refl

-- Cite from relative monads paper.
eqApp2 : ∀{i j k}{A : Set i}{B : A → Set j}{C : Set k}{a a' : A} → a ≅ a' → {b : B a}{b' : B a'} → b ≅ b' → 
            (f : (a : A) → B a → C) → f a b ≅ f a' b'
eqApp2 refl refl f = refl

eqApp3 : ∀{l}{A : Set l}{B : Set (suc l)}{C : A → Set (suc l)}{D : Set (suc l)}
        (f : (x : A)(y : B)(z : C x) → D) →
        {a a' : A} → a ≅ a' → 
        {b : B}{b' : B} → b ≅ b' → 
        {c : C a}{c' : C a'} → c ≅ c' → 
        f a b c ≅ f a' b' c'
eqApp3 f refl refl refl = refl

feqApp3' : ∀{l}{A : Set l}{B : Set (suc l)}{C : A → Set (suc l)}{D : Set (suc l)}
        (f  : (x : A)(y : B)(z : C x) → D) →
        (f' : (x : A)(y : B)(z : C x) → D) →
        f ≅ f' →
        {a : A} →
        f a  ≅ f' a 
feqApp3' f f' p {a} = eqApp {f = λ h → h a} p

depfeqApp3a : ∀{l}{A : Set l}{B : Set (suc l)}{C : A → Set (suc l)}{D : Set (suc l)}
        (f  : (x : A)(y : B)(z : C x) → D) →
        (f' : (x : A)(y : B)(z : C x) → D) →
        f ≅ f' →
        {a : A}{b : B} {c : C a} →
        f a b c ≅ f' a b c
depfeqApp3a {_}{A}{B}{C} f f' p {a}{b}{c} = 
        feqApp {f = f a b} {f' = f' a b} (feqApp {f = f a} {f' = f' a} (eqApp {f = λ h → h a} p) refl) refl

depfeqApp3b : ∀{l}{A : Set l}{B : A → Set (suc l)}{C : A → Set (suc l)}{D : Set (suc l)}
        (f  : (x : A)(y : B x)(z : C x) → D) →
        (f' : (x : A)(y : B x)(z : C x) → D) →
        f ≅ f' →
        {a : A}{b : B a} {c : C a} →
        f a b c ≅ f' a b c
depfeqApp3b {_}{A}{B}{C} f f' p {a}{b}{c} = 
        feqApp {f = f a b} {f' = f' a b} (feqApp {f = f a} {f' = f' a} (eqApp {f = λ h → h a} p) refl) refl

depfeqApp3c : ∀{l}{A : Set l}{B : A → A → Set (suc l)}{C : A → Set (suc l)}{D : Set (suc l)}
        (f  : (x : A)(y : B x x)(z : C x) → D) →
        (f' : (x : A)(y : B x x)(z : C x) → D) →
        f ≅ f' →
        {a : A}{b : B a a} {c : C a} →
        f a b c ≅ f' a b c
depfeqApp3c {_}{A}{B}{C} f f' p {a}{b}{c} = 
            feqApp {f = f a b} {f' = f' a b} (feqApp {f = f a} {f' = f' a} (eqApp {f = λ h → h a} p) refl) refl

depfeqApp3d : ∀{l}{A : Set l}{B : A → A → Set (suc l)}{C : A → A → Set (suc l)}{D : Set (suc l)}
        (f  : (x : A)(y : B x x)(z : C x x) → D) →
        (f' : (x : A)(y : B x x)(z : C x x) → D) →
        f ≅ f' →
        {a : A}{b : B a a} {c : C a a} →
        f a b c ≅ f' a b c
depfeqApp3d {_}{A}{B}{C} f f' p {a}{b}{c} = 
            feqApp {f = f a b} {f' = f' a b} (feqApp {f = f a} {f' = f' a} (eqApp {f = λ h → h a} p) refl) refl

depfeqApp3e : ∀{l}{A : Set l}{B : Set (suc l)}{C : A → A → Set (suc l)}{D : Set (suc l)}
        (f  : (x : A)(y : B)(z : C x x) → D) →
        (f' : (x : A)(y : B)(z : C x x) → D) →
        f ≅ f' →
        {a : A}{b : B} {c : C a a} →
        f a b c ≅ f' a b c
depfeqApp3e {_}{A}{B}{C} f f' p {a}{b}{c} = 
            feqApp {f = f a b} {f' = f' a b} (feqApp {f = f a} {f' = f' a} (eqApp {f = λ h → h a} p) refl) refl


depfeqAppa : ∀{l l' l'' l'''}{A : Set l}{B : Set l'}{C : A → B → Set l''}{D : A → B → Set  l'''}{a : A}
        (f  : (x : A)(y : B)(z : C x y) → D x y) →
        (f' : (x : A)(y : B)(z : C x y) → D x y) →
        f ≅ f' →        
        f a ≅ f' a
depfeqAppa {l}{l'}{l''}{l'''}{A}{B}{C}{D}{a} f f' p = eqApp {f = λ h → h a} p

depfeqApp2a : ∀{l l' l'' l'''}{A : Set l}{B : Set  l'}{C : A → B → Set  l''}{D : A → B → Set l'''}{a : A}
        (f  : (y : B)(z : C a y) → D a y) →
        (f' : (y : B)(z : C a y) → D a y) →
        f ≅ f' →
        {b : B} {c : C a b} →
        f b c ≅ f' b c
depfeqApp2a f f' p {b} {c} = feqApp {f = f b} {f' = f' b} (eqApp {f = λ h → h b} p) refl

depfeqApp3f : ∀{l l' l'' l'''}{A : Set l}{B : Set l'}{C : A → B → Set l''}{D : A → B → Set l'''}
        (f  : (x : A)(y : B)(z : C x y) → D x y) →
        (f' : (x : A)(y : B)(z : C x y) → D x y) →
        f ≅ f' →
        {a : A}{b : B} {c : C a b} →
        f a b c ≅ f' a b c
depfeqApp3f {_}{_}{_}{_}{A}{B}{C}{D} f f' p {a}{b}{c} = 
                         depfeqApp2a {A = A} {B = B}{C = λ o1 o2 → C o1 o2}
                           {D = λ o1₁ o2₁ → D o1₁ o2₁} (f a) (f' a) (eqApp {f = λ h → h a} p) {b} {c}

depfeqApp3g : ∀{l l' l'' l'''}{A : Set l}{B : Set l'}{C : A → B → Set l''}{D D' : A → B → Set l'''}
        (f  : (x : A)(y : B)(z : C x y) → D x y) →
        (f' : (x : A)(y : B)(z : C x y) → D' x y) →
        D ≅ D' → 
        f ≅ f' →
        {a : A}{b : B} {c : C a b} →
        f a b c ≅ f' a b c
depfeqApp3g {_}{_}{_}{_}{A}{B}{C}{D} f f' refl p {a}{b}{c} = 
                         depfeqApp2a {A = A} {B = B} {C = λ o1₁ o2₁ → C o1₁ o2₁} {D = λ o1 o2 → D o1 o2} (f a) (f' a) (eqApp {f = λ h → h a} p) {b} {c}

idepfeqApp2a : ∀{l l' l'' l''' l''''}{A : Set l}{B : Set  l'}{C : Set l''}{D : A → B → C → Set  l'''}{E : A → B → C → Set l''''}{a : A}
        (f  : {x : B}{y : C}(z : D a x y) → E a x y) →
        (f' : {x : B}{y : C}(z : D a x y) → E a x y) →
        (∀{x y} → f {x}{y}  ≅ f' {x}{y}) →
        {b : B}{c : C}{m : D a b c} →
        f {b}{c} m ≅ f' {b} {c} m
idepfeqApp2a {l}{l'}{l''}{l'''}{l''''}{A}{B}{C}{D}{E}{a} f f' p {b}{c}{m} = 
             feqApp {f = f {b} {c}} {f' = f' {b} {c}} {m} {m} (ext (λ h → feqApp {f = f {b} {c}} {f' = f' {b} {c}} {h} {h} (p {b}{c}) refl)) refl

depfeqApp2b : ∀{l l' l''}{A : Set l}{D : A → A → Set l'}{E E' : A → A → Set l''}
        (f  : (x : A)(y : A)(z : A) → (m1 : D y z) → (m2 : D x y) → E x z) →
        {f'  : (x : A)(y : A)(z : A) → (m1 : D y z) → (m2 : D x y) → E' x z} →
        E ≅ E' →
        f ≅ f' →
        {a a' b b' c c' : A}{m1 : D b c}{m2 : D a b}{m1' : D  b' c'}{m2' : D a' b'} →
        a ≅ a' → b ≅ b' → c ≅ c' → m1 ≅ m1' → m2 ≅ m2' →
        f a b c m1 m2 ≅ f' a' b' c' m1' m2'
depfeqApp2b {_}{_}{_}{A}{D}{E} f refl refl {a = a}{b = b}{c = c}{m1 = m1}{m2 = m2}  refl refl refl refl refl = 
  eqApp {f = f a b c m1} {m2}{m2} refl

feqApp3 : ∀{l}{A : Set l}{B : A → Set (suc l)}{C : A → Set (suc l)}{D : Set (suc l)}
        (f  : (x : A)(y : B x)(z : C x) → D) →
        (f' : (x : A)(y : B x)(z : C x) → D) →
        f ≅ f' →
        {a : A}{b : B a} {c : C a} →
        f a b c ≅ f' a b c
feqApp3 {_}{A}{B}{C} f f' p {a}{b}{c} = 
        feqApp {f = f a b} {f' = f' a b} (feqApp {f = f a} {f' = f' a} (eqApp {f = λ h → h a} p) refl) refl

coerce : ∀{l}{A B : Set l} → A ≅ B → A → B
coerce refl a = a

p : ∀{m}{A B : Set m}{a : A}{b : B} → (q : B ≅ A) → _≅_ {m} {A} a {A} (coerce q b) → _≅_ {m} {A} a {B} b
p refl refl = refl

eqApp4 : ∀{x y z v w}{A : Set x}{B : A → Set y}{C : (a : A) → B a → Set z}{D : (a : A)(b : B a) → C a b  → Set v}{E : Set w}
             (f : (a : A)(b : B a)(c : C a b) → D a b c → E) → 
             {a a' : A} → a ≅ a' → 
             {b : B a}{b' : B a'} → b ≅ b' → 
             {c : C a b}{c' : C a' b'} → c ≅ c' → 
             {d : D a b c}{d' : D a' b' c'} → d ≅ d' → 
             f a b c d ≅ f a' b' c' d'
eqApp4 f refl refl refl refl = refl

funCong : ∀{l m : Level}{A : Set l}{B : Set m}{f g : A → B}{a : A}{b : B}
  → (p : f ≅ g) → (q : f a ≅ b) 
  → (w : g a ≅ b) → q ≅ w
funCong refl q w = ir

funCong2 : ∀{l : Level}{A B B' X Y : Set l}{f : ∀{X Y} → A → B}{g : ∀{X Y} → A → B'}{a : A}{b : B}
  → (r : B ≅ B') → (p : (λ {X}{Y} → f {X}{Y}) ≅ (λ {X}{Y} → g {X}{Y})) → (q : f {X}{Y} a ≅ b) 
  → (w : g {X}{Y} a ≅ b) → q ≅ w
funCong2 refl refl q w = ir

fixtypes : ∀{x}{A A' : Set x}{a a' : A}{a'' a''' : A'}{p : a ≅ a'}{q : a'' ≅ a'''} → a ≅ a'' → a' ≅ a''' → p ≅ q
fixtypes refl refl = ir  
