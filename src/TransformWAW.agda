{-# OPTIONS --safe #-}

-- | Write-after-Write elimination specification
module TransformWAW where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Function using (_∘_)
open import Relation.Unary using (_∈_)
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.LIMM as LIMM


open Execution


--
-- WAW: X = v'; X = v  ↦  X = v
--      ^
--      |
--     This Write becomes a Skip
--


record WAW-Restricted (ex : Execution LabelLIMM) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsLIMMConsistent ex

    -- | The skip event that overwrites the eliminated read.
    elim-ev      : Event LabelLIMM
    elim-ev-skip : elim-ev ∈ EvSkip
    
    preserved-ev     : Event LabelLIMM
    -- non-init relaxed write
    preserved-ev-wₙᵣ : preserved-ev ∈ EvWₙₜ tmov

    transform-pair : po-imm ex elim-ev preserved-ev



module Extra {ex : Execution LabelLIMM} (ex-ok : WAW-Restricted ex) where

  open WAW-Restricted ex-ok

  -- # Helpers

  -- relaxed write
  preserved-ev-wᵣ : EvWₜ tmov preserved-ev
  preserved-ev-wᵣ = wₙₜ⇒wₜ preserved-ev-wₙᵣ

  preserved-ev-w : EvW preserved-ev
  preserved-ev-w = wₙₜ⇒w preserved-ev-wₙᵣ

  elim-uid : UniqueId
  elim-uid = ev-uid elim-ev

  elim-has-uid : HasUid elim-uid elim-ev
  elim-has-uid = ev-has-uid _

  elim-tid : ThreadId
  elim-tid = skip-tid elim-ev-skip

  elim-loc : Location
  elim-loc = w-loc preserved-ev-w

  elim-val : Value
  elim-val = w-val preserved-ev-w

  preserved∈ex : preserved-ev ∈ events ex
  preserved∈ex = piʳ∈ex wf transform-pair

  elim∈ex : elim-ev ∈ events ex
  elim∈ex = piˡ∈ex wf transform-pair

  preserved-has-loc : HasLoc elim-loc preserved-ev
  preserved-has-loc = w-has-loc preserved-ev-w

  preserved-has-val : HasVal elim-val preserved-ev
  preserved-has-val = w-has-val preserved-ev-w


-- | Relates the events in the source and target executions, following the
-- transformation on the instructions.
--
-- If the source has the additional write event, then - by WellFormedness - it is part of the execution.
record WAWMapping (src : Execution LabelLIMM) {dst : Execution LabelLIMM} (dst-res : WAW-Restricted dst) : Set where
  open WAW-Restricted dst-res
  open Extra dst-res

  field
    src-elim-ev     : Event LabelLIMM
    src-elim-ev-def : src-elim-ev ≡ event elim-uid elim-tid (lab-w tmov elim-loc elim-val)
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelLIMM} → x ≢ elim-ev → x ∈ events dst → x ∈ events src
