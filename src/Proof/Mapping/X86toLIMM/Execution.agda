{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import MapX86toLIMM using (LIMM-X86Restricted)


module Proof.Mapping.X86toLIMM.Execution
  (dst : Execution LabelLIMM)
  (dst-wf : WellFormed dst)
  (dst-ok : LIMM-X86Restricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Unary using (Pred; _∈_; _∉_)
-- Library imports
open import Dodo.Unary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.LIMM as LIMM
open import Arch.X86 as X86
-- Local imports: Theorem Specification
open import MapX86toLIMM
-- Local imports: Proof Components
import Proof.Framework LabelX86 dst dst-wf as Ψ
import Proof.Mapping.Framework LabelX86 dst dst-wf as Δ



open Ex.Execution
open Ex.WellFormed
open IsLIMMConsistent


-- # Backward Mapping of Relations

-- Instruction mapping:
--
-- RMOV   ↦ LD;F_LD_M
-- WMOV   ↦ F_ST_ST;ST
-- RMW    ↦ RMW
-- MFENCE ↦ F_SC
--
-- Corresponding event mapping:
--
-- Rᵣ(x,v)             ↦ Rᵣ(x,v);F_RM
-- W(x,v)              ↦ F_WW;Wᵣ(x,v)
-- Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;Wₗ(x,v')  || successful RMW
-- Rₗ(x,v)             ↦ Rₗ(x,v)               || failed RMW
-- F                   ↦ F_SC


ev[⇐] : {x : Event LabelLIMM}
  → (x∈dst : x ∈ events dst)
    ------------------------
  → Event LabelX86
ev[⇐] {event-init uid loc val}            x∈dst = event-init uid loc val
ev[⇐] {event-skip uid tid}                x∈dst = event-skip uid tid
ev[⇐] {event uid tid (lab-r tag loc val)} x∈dst = event uid tid (lab-r tag loc val)
ev[⇐] {event uid tid (lab-w tag loc val)} x∈dst = event uid tid (lab-w tag loc val)
ev[⇐] {event uid tid (lab-f RM)}          x∈dst = event-skip uid tid
ev[⇐] {event uid tid (lab-f WW)}          x∈dst = event-skip uid tid
ev[⇐] {event uid tid (lab-f SC)}          x∈dst = event uid tid lab-f


-- # Proof framework

open Ψ.Definitions ev[⇐]

uid[⇐] : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
uid[⇐] {_}                           x∈dst has-uid-init = has-uid-init
uid[⇐] {_}                           x∈dst has-uid-skip = has-uid-skip
uid[⇐] {_} {event _ _ (lab-r _ _ _)} x∈dst has-uid      = has-uid
uid[⇐] {_} {event _ _ (lab-w _ _ _)} x∈dst has-uid      = has-uid
uid[⇐] {_} {event _ _ (lab-f RM)}    x∈dst has-uid      = has-uid-skip
uid[⇐] {_} {event _ _ (lab-f WW)}    x∈dst has-uid      = has-uid-skip
uid[⇐] {_} {event _ _ (lab-f SC)}    x∈dst has-uid      = has-uid

uid[$⇒] : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}        x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}          x∈dst has-uid-skip = has-uid-skip
uid[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst has-uid      = has-uid
uid[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst has-uid      = has-uid
uid[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst has-uid-skip = has-uid
uid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst has-uid-skip = has-uid
uid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst has-uid      = has-uid


tid[⇐] : {tid : ThreadId} → Pred[⇐]² (HasTid tid)
tid[⇐] {_}                           x∈dst has-tid-skip = has-tid-skip
tid[⇐] {_} {event _ _ (lab-r _ _ _)} x∈dst has-tid      = has-tid
tid[⇐] {_} {event _ _ (lab-w _ _ _)} x∈dst has-tid      = has-tid
tid[⇐] {_} {event _ _ (lab-f RM)}    x∈dst has-tid      = has-tid-skip
tid[⇐] {_} {event _ _ (lab-f WW)}    x∈dst has-tid      = has-tid-skip
tid[⇐] {_} {event _ _ (lab-f SC)}    x∈dst has-tid      = has-tid

tid[$⇒] : {tid : ThreadId} → Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}          x∈dst has-tid-skip = has-tid-skip
tid[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst has-tid      = has-tid
tid[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst has-tid      = has-tid
tid[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst has-tid-skip = has-tid
tid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst has-tid-skip = has-tid
tid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst has-tid      = has-tid


loc[⇐] : {loc : Location} → Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init          = has-loc-init
loc[⇐] x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[⇐] x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl

loc[$⇒] : {loc : Location} → Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init x x₁ x₂} x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl
loc[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst ()
loc[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst ()
loc[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (has-loc-r () _)
loc[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (has-loc-w () _)


val[⇐] : {val : Value} → Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init          = has-val-init
val[⇐] x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[⇐] x∈dst (has-val-w is-w refl) = has-val-w is-w refl

val[$⇒] : {val : Value} → Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init x x₁ x₂} x∈dst has-val-init = has-val-init
val[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-val-w is-w refl) = has-val-w is-w refl
val[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst ()
val[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst ()
val[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (has-val-r () _)
val[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (has-val-w () _)


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init


Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _} x∈dst ev-init = ev-init
-- impossible cases
Init[$⇒] {event _ _ (lab-f RM)} x∈dst ()
Init[$⇒] {event _ _ (lab-f WW)} x∈dst ()
Init[$⇒] {event _ _ (lab-f SC)} x∈dst ()


Wₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] x∈dst (ev-init refl)   = ev-init refl
Wₜ[⇐] x∈dst (ev-w is-w refl) = ev-w is-w refl


Wₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}        x∈dst (ev-init refl)   = ev-init refl
Wₜ[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (ev-w is-w refl) = ev-w is-w refl
-- impossible cases
Wₜ[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (ev-w () _)


Rₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] x∈dst (ev-r is-r refl) = ev-r is-r refl


Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (ev-r is-r refl) = ev-r is-r refl
-- impossible cases
Rₜ[$⇒] {_} {event-init _ _ _}        x∈dst ()
Rₜ[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst (ev-r () _)


ψ : Ψ.GeneralFramework
ψ =
  record
    { ev[⇐]    = ev[⇐]
    ; uid[⇐]   = uid[⇐]
    ; uid[$⇒]  = uid[$⇒]
    ; tid[⇐]   = tid[⇐]
    ; tid[$⇒]  = tid[$⇒]
    ; Init[⇐]  = Init[⇐]
    ; Init[$⇒] = Init[$⇒]
    }

δ : Δ.MappingFramework
δ =
  record
    { ψ       = ψ
    ; loc[⇐]  = loc[⇐]
    ; loc[$⇒] = loc[$⇒]
    ; val[⇐]  = val[⇐]
    ; val[$⇒] = val[$⇒]
    ; Wₜ[⇐]   = Wₜ[⇐]
    ; Wₜ[$⇒]  = Wₜ[$⇒]
    ; Rₜ[⇐]   = Rₜ[⇐]
    ; Rₜ[$⇒]  = Rₜ[$⇒]
    }


-- # Extra helpers

module Extra where

  open Δ.Definitions δ
  open Ψ.WellFormed ψ using (rmw[⇒])
  

  R₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (X86.EvR₌ tag loc val) (LIMM.EvR₌ tag loc val)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-r _ _ _)} x∈dst ev-r = ev-r₌
  -- impossible cases
  R₌[$⇒] {_} {_} {_} {event-init _ _ _}        x∈dst ()
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-w _ _ _)} x∈dst ()
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}    x∈dst ()

  R₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (X86.EvR₌ tag loc val) (LIMM.EvR₌ tag loc val)
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  W₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (X86.EvW₌ tag loc val) (LIMM.EvW₌ tag loc val)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-w _ _ _)} x∈dst ev-w₌ = ev-w₌
  -- impossible cases
  W₌[$⇒] {_} {_} {_} {event-init _ _ _}        x∈dst ()
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-r _ _ _)} x∈dst ()
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}    x∈dst ()

  W₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (X86.EvW₌ tag loc val) (LIMM.EvW₌ tag loc val)
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]
  

  F[$⇒] : Pred[$⇒] EvF (EvF₌ SC)
  F[$⇒] {event _ _ (lab-f SC)} x∈dst (ev-f is-f) = ev-f₌
  -- impossible cases
  F[$⇒] {event _ _ (lab-r _ _ _)} x∈dst (ev-f ())
  F[$⇒] {event _ _ (lab-w _ _ _)} x∈dst (ev-f ())

  F[⇒] : Pred[⇒] EvF (EvF₌ SC)
  F[⇒] = [$⇒]→₁[⇒] F[$⇒]
