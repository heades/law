module Setoid.Total where

open import level
open import Relation

record SetT {l : level} : Set (lsuc l) where
 field 
   el : Set l
   R  : el → el → Set l
   eqRpf : EqRel R


