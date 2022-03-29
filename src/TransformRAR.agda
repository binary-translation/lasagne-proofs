{-# OPTIONS --safe #-}


-- | Read-after-read transformation
module TransformRAR where

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
-- RAR: a = X; b = X  ->  a = X; b = a
--             ^
--             |
--            This Read becomes a Skip
--

record RAR-Restricted (ex : Execution LabelLIMM) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsLIMMConsistent ex

    -- | The skip event that overwrites the eliminated read.
    elim-ev      : Event LabelLIMM
    elim-ev-skip : elim-ev ∈ EvSkip
    
    preserved-ev   : Event LabelLIMM
    preserved-ev-r : preserved-ev ∈ EvRₜ tmov

    transform-pair : po-imm ex preserved-ev elim-ev
  

module Extra {ex : Execution LabelLIMM} (ex-ok : RAR-Restricted ex) where

  open RAR-Restricted ex-ok

  elim-uid : UniqueId
  elim-uid = ev-uid elim-ev

  elim-has-uid : HasUid elim-uid elim-ev
  elim-has-uid = ev-has-uid _

  elim-tid : ThreadId
  elim-tid = skip-tid elim-ev-skip

  elim-loc : Location
  elim-loc = r-loc (rₜ⇒r preserved-ev-r)

  elim-val : Value
  elim-val = r-val (rₜ⇒r preserved-ev-r)

  preserved∈ex : preserved-ev ∈ events ex
  preserved∈ex = piˡ∈ex wf transform-pair

  elim∈ex : elim-ev ∈ events ex
  elim∈ex = piʳ∈ex wf transform-pair

  preserved-has-loc : HasLoc elim-loc preserved-ev
  preserved-has-loc = r-has-loc (rₜ⇒r preserved-ev-r)

  preserved-has-val : HasVal elim-val preserved-ev
  preserved-has-val = r-has-val (rₜ⇒r preserved-ev-r)


-- | Relates the events in the source and target executions, following the
-- transformation on the instructions.
--
-- If the source has the additional read event, then - by WellFormedness - it is part of the execution.
record RARMapping (src : Execution LabelLIMM) {dst : Execution LabelLIMM} (dst-res : RAR-Restricted dst) : Set where
  open RAR-Restricted dst-res
  open Extra dst-res

  field
    src-elim-ev     : Event LabelLIMM
    src-elim-ev-def : src-elim-ev ≡ event elim-uid elim-tid (lab-r tmov elim-loc elim-val)
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelLIMM} → x ≢ elim-ev → x ∈ events dst → x ∈ events src
