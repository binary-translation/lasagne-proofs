{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder21 using (ReorderRestricted21; ReordersTo21)


module Proof.Reorder.Reorder21.Mapping
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted21 dst)
  where


-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Proof Components
open import Proof.Reorder.Reorder21.Execution dst dst-res


proof-mapping : ReordersTo21 src dst-res
proof-mapping =
  record
    { events-preserved = ≡-to-⇔₁ refl
    ; co-preserved     = ≡-to-⇔₂ refl
    ; rf-preserved     = ≡-to-⇔₂ refl
    ; rmw-preserved    = ≡-to-⇔₂ refl
    ; po-preserved⇒    = po[⇒]
    ; po-preserved⇐    = po[⇐]
    }
