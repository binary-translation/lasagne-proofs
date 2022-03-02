{-# OPTIONS --safe #-}


-- | Read-after-write elimination specification
module TransformRAW where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Function using (_∘_)
open import Relation.Unary using (_∈_)
-- Library imports
open import Dodo.Unary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.LIMM as LIMM


open Execution


--
-- RAW: X = v; a = X  ->  X = v; a = v
--             ^
--             |
--            This Read becomes a Skip
--


-- | We assume the LIMM program is obtained through mapping a x86 program.
--
-- This means that /not/ all fences can be present in the execution. If all
-- fences were present, this mapping is /incorrect/ in general.
data RAWEvent : Event LabelLIMM → Set where
  raw-init : {uid : UniqueId} {loc : Location} {val : Value} → RAWEvent (event-init uid loc val)
  raw-skip : {uid : UniqueId} {tid : ThreadId} → RAWEvent (event-skip uid tid)
  raw-r : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → RAWEvent (event uid tid (lab-r tag loc val))
  raw-w : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → RAWEvent (event uid tid (lab-w tag loc val))
  raw-f-sc : {uid : UniqueId} {tid : ThreadId} → RAWEvent (event uid tid (lab-f SC))
  raw-f-rm : {uid : UniqueId} {tid : ThreadId} → RAWEvent (event uid tid (lab-f RM))
  raw-f-ww : {uid : UniqueId} {tid : ThreadId} → RAWEvent (event uid tid (lab-f WW))


record RAW-Restricted (ex : Execution LabelLIMM) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsLIMMConsistent ex

    events-bound : events ex ⊆₁ RAWEvent

    -- | The skip event that overwrites the eliminated read.
    elim-ev      : Event LabelLIMM
    elim-ev-skip : elim-ev ∈ EvSkip
    
    preserved-ev     : Event LabelLIMM
    -- non-init relaxed write
    preserved-ev-wₙᵣ : preserved-ev ∈ EvWₙₜ tmov

    transform-pair : po-imm ex preserved-ev elim-ev


module Extra {ex : Execution LabelLIMM} (ex-ok : RAW-Restricted ex) where

  open RAW-Restricted ex-ok

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
  preserved∈ex = piˡ∈ex wf transform-pair

  elim∈ex : elim-ev ∈ events ex
  elim∈ex = piʳ∈ex wf transform-pair

  preserved-has-loc : HasLoc elim-loc preserved-ev
  preserved-has-loc = w-has-loc preserved-ev-w

  preserved-has-val : HasVal elim-val preserved-ev
  preserved-has-val = w-has-val preserved-ev-w


-- | Relates the source and target executions.
--
-- If the source has the additional write event, then - by WellFormedness - it is part of the execution.
record RAWMapping (src : Execution LabelLIMM) {dst : Execution LabelLIMM} (dst-res : RAW-Restricted dst) : Set where
  open RAW-Restricted dst-res
  open Extra dst-res

  field
    src-elim-ev     : Event LabelLIMM
    src-elim-ev-def : src-elim-ev ≡ event elim-uid elim-tid (lab-r tmov elim-loc elim-val)
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelLIMM} → x ≢ elim-ev → x ∈ events dst → x ∈ events src
