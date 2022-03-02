{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.Armv8 using (LabelArmv8)
open import MapLIMMtoArmv8 using (Armv8-LIMMRestricted)


module Proof.Mapping.LIMMtoArmv8.Execution
  (dst : Execution LabelArmv8)
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-LIMMRestricted dst)
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
open import Arch.Armv8 as Armv8
-- Local imports: Theorem Specification
open import MapLIMMtoArmv8
-- Local imports: Proof Components
import Proof.Framework LabelLIMM dst dst-wf as Ψ
import Proof.Mapping.Framework LabelLIMM dst dst-wf as Δ


open Ex.Execution
open IsArmv8Consistent
open Armv8-LIMMRestricted dst-ok


-- # Backward Mapping of Relations

--
-- The mapping:
--
-- Rᵣ         ↦  Rᵣ
-- Wᵣ         ↦  Wᵣ
-- Rₗ;rmw;Wₗ  ↦  F_FULL;Rₗ;lxsx;Wₗ;F_FULL  || successful RMW
-- Rₗ         ↦  F_FULL;Rₗ;F_FULL          || failed RMW
-- F_RM       ↦  F_LD
-- F_WW       ↦  F_ST
-- F_SC       ↦  F_FULL
--

ev[⇐] : {x : Event LabelArmv8} → (x∈dst : x ∈ events dst) → Event LabelLIMM
ev[⇐] {event-init uid loc val}          x∈dst = event-init uid loc val
ev[⇐] {event-skip uid tid}              x∈dst = event-skip uid tid
ev[⇐] {event uid tid (lab-r t loc val)} x∈dst = event uid tid (lab-r t loc val)
ev[⇐] {event uid tid (lab-w t loc val)} x∈dst = event uid tid (lab-w t loc val)
ev[⇐] x@{event uid tid (lab-f F-full)}  x∈dst with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
... | inj₁ _ = event-skip uid tid -- pre/post rmw
... | inj₂ _ = event uid tid (lab-f SC)
ev[⇐] {event uid tid (lab-f F-ld)}      x∈dst = event uid tid (lab-f RM)
ev[⇐] {event uid tid (lab-f F-st)}      x∈dst = event uid tid (lab-f WW)
-- absent events
ev[⇐] {event _ _ (lab-a _ _ _)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event _ _ (lab-q _ _)}   x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event _ _ (lab-l _ _ _)} x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
ev[⇐] {event _ _ lab-isb}       x∈dst = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


-- # Proof framework

open Ψ.Definitions ev[⇐]

uid[⇐] : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
uid[⇐] {_}                            x∈dst has-uid-init = has-uid-init
uid[⇐] {_}                            x∈dst has-uid-skip = has-uid-skip
uid[⇐] {_} {event _ _ (lab-r _ _ _)}  x∈dst has-uid = has-uid
uid[⇐] {_} {event _ _ (lab-w _ _ _)}  x∈dst has-uid = has-uid
uid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-uid with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
uid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-uid | inj₁ _ = has-uid-skip
uid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-uid | inj₂ _ = has-uid
uid[⇐] {_} {event _ _ (lab-f F-ld)}   x∈dst has-uid = has-uid
uid[⇐] {_} {event _ _ (lab-f F-st)}   x∈dst has-uid = has-uid
-- impossible cases
uid[⇐] {_} {event _ _ (lab-a _ _ _)} x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event _ _ (lab-q _ _)}   x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event _ _ (lab-l _ _ _)} x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[⇐] {_} {event _ _ lab-isb}       x∈dst has-uid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


uid[$⇒] : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}         x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}           x∈dst has-uid-skip = has-uid-skip
uid[$⇒] {_} {event _ _ (lab-r _ _ _)}  x∈dst has-uid = has-uid
uid[$⇒] {_} {event _ _ (lab-w _ _ _)}  x∈dst has-uid = has-uid
uid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
uid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst has-uid-skip | inj₁ _ = has-uid
uid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst has-uid      | inj₂ _ = has-uid
uid[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst has-uid = has-uid
uid[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst has-uid = has-uid
-- impossible cases
uid[$⇒] {_} {event _ _ (lab-a _ _ _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event _ _ (lab-q _ _)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event _ _ (lab-l _ _ _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
uid[$⇒] {_} {event _ _ lab-isb}       x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


tid[⇐] : {tid : ThreadId} → Pred[⇐]² (HasTid tid)
tid[⇐]                                x∈dst has-tid-skip = has-tid-skip
tid[⇐] {_} {event _ _ (lab-r _ _ _)}  x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ (lab-w _ _ _)}  x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-tid with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
tid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-tid | inj₁ _ = has-tid-skip
tid[⇐] {_} {event _ _ (lab-f F-full)} x∈dst has-tid | inj₂ _ = has-tid
tid[⇐] {_} {event _ _ (lab-f F-ld)}   x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ (lab-f F-st)}   x∈dst has-tid = has-tid
-- impossible cases
tid[⇐] {_} {event _ _ (lab-a _ _ _)} x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event _ _ (lab-q _ _)}   x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event _ _ (lab-l _ _ _)} x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[⇐] {_} {event _ _ lab-isb}       x∈dst has-tid = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


tid[$⇒] : {tid : ThreadId} → Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}           x∈dst has-tid-skip = has-tid-skip
tid[$⇒] {_} {event _ _ (lab-r _ _ _)}  x∈dst has-tid = has-tid
tid[$⇒] {_} {event _ _ (lab-w _ _ _)}  x∈dst has-tid = has-tid
tid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
tid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst has-tid-skip | inj₁ _ = has-tid
tid[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst has-tid      | inj₂ _ = has-tid
tid[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst has-tid = has-tid
tid[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst has-tid = has-tid
-- impossible cases
tid[$⇒] {_} {event _ _ (lab-a _ _ _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event _ _ (lab-q _ _)}   x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event _ _ (lab-l _ _ _)} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())
tid[$⇒] {_} {event _ _ lab-isb}       x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst λ())


loc[⇐] : {loc : Location} → Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init          = has-loc-init
loc[⇐] x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[⇐] x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl
-- impossible cases
loc[⇐] x∈dst (has-loc-r is-a refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] x∈dst (has-loc-r is-q refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[⇐] x∈dst (has-loc-w is-l refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


loc[$⇒] : {loc : Location} → Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}        x∈dst has-loc-init          = has-loc-init
loc[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl
-- impossible cases
loc[$⇒] {_} {event-skip _ _} x∈dst ()
loc[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
loc[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst (has-loc-r () _) | inj₂ _
loc[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst (has-loc-w () _) | inj₂ _
loc[$⇒] {_} {event _ _ (lab-a _ _ _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-q _ _)}    x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-l _ _ _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ lab-isb}        x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
loc[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst x-loc = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))
loc[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst x-loc = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))


val[⇐] : {val : Value} → Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init          = has-val-init
val[⇐] x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[⇐] x∈dst (has-val-w is-w refl) = has-val-w is-w refl
-- impossible cases
val[⇐] x∈dst (has-val-r is-a refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] x∈dst (has-val-r is-q refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[⇐] x∈dst (has-val-w is-l refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


val[$⇒] : {val : Value} → Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}        x∈dst has-val-init          = has-val-init
val[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-val-w is-w refl) = has-val-w is-w refl
-- impossible cases
val[$⇒] {_} {event-skip _ _}           x∈dst ()
val[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
val[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst (has-val-r () _) | inj₂ _
val[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst (has-val-w () _) | inj₂ _
val[$⇒] {_} {event _ _ (lab-a _ _ _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-q _ _)}    x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-l _ _ _)}  x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ lab-isb}        x∈dst _     = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
val[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst x-val = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))
val[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst x-val = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init


Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _}         x∈dst ev-init = ev-init
-- impossible cases
Init[$⇒] {event-skip _ _}           x∈dst ()
Init[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
Init[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ _
Init[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
Init[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Init[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Wₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] x∈dst (ev-init refl)   = ev-init refl
Wₜ[⇐] x∈dst (ev-w is-w refl) = ev-w is-w refl
Wₜ[⇐] x∈dst (ev-w is-l refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Wₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}        x∈dst (ev-init refl)   = ev-init refl
Wₜ[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (ev-w is-w refl) = ev-w is-w refl
-- impossible cases
Wₜ[$⇒] {_} {event-skip _ _}           x∈dst ()
Wₜ[$⇒] {_} {event _ _ (lab-r _ _ _)}  x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
Wₜ[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst (ev-w () _) | inj₂ _
Wₜ[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Wₜ[$⇒] {_} {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Rₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] x∈dst (ev-r is-r refl) = ev-r is-r refl
-- impossible cases
Rₜ[⇐] x∈dst (ev-r is-a refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[⇐] x∈dst (ev-r is-q refl) = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))


Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event _ _ (lab-r _ _ _)}  x∈dst (ev-r is-r refl) = ev-r is-r refl
-- impossible cases
Rₜ[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
Rₜ[$⇒] {_} {event _ _ (lab-f F-full)} x∈dst (ev-r () _) | inj₂ _
Rₜ[$⇒] {_} {event-skip _ _} x∈dst ()
Rₜ[$⇒] {_} {event _ _ (lab-w _ _ _)}  x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ (lab-f F-ld)}   x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ (lab-f F-st)}   x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ (lab-l _ _ _ )} x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
Rₜ[$⇒] {_} {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))

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
    → Pred[$⇒] (LIMM.EvR₌ tag loc val) (Armv8.EvR₌ tag loc val)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-r _ _ _)}  x∈dst ev-r₌ = ev-r₌
  -- impossible cases
  R₌[$⇒] {_} {_} {_} {event-skip _ _} x∈dst ()
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst () | inj₁ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  
  R₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (LIMM.EvR₌ tag loc val) (Armv8.EvR₌ tag loc val)
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  W₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (LIMM.EvW₌ tag loc val) (Armv8.EvW₌ tag loc val)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-w _ _ _)}  x∈dst ev-w₌ = ev-w₌
  -- impossible cases
  W₌[$⇒] {_} {_} {_} {event-skip _ _}           x∈dst ()
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst () | inj₁ _
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
  
  W₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (LIMM.EvW₌ tag loc val) (Armv8.EvW₌ tag loc val)
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]


  -- Map fences. RM / WW / SC
  --
  -- RM  ->  F-ld
  -- WW  ->  F-st
  -- SC  ->  F-full

  Frm[$⇒] : Pred[$⇒] (LIMM.EvF₌ RM) (Armv8.EvF₌ F-ld)
  Frm[$⇒] {event _ _ (lab-f F-ld)}   x∈dst _ = ev-f₌
  -- impossible cases
  Frm[$⇒] {event-init _ _ _}         x∈dst ()
  Frm[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Frm[$⇒] {event-skip _ _}           x∈dst ()
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ _
  Frm[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _
    
  Frm[⇒] : Pred[⇒] (LIMM.EvF₌ RM) (Armv8.EvF₌ F-ld)
  Frm[⇒] = [$⇒]→₁[⇒] Frm[$⇒]
  

  Fww[$⇒] : Pred[$⇒] (LIMM.EvF₌ WW) (Armv8.EvF₌ F-st)
  Fww[$⇒] {event _ _ (lab-f F-st)}   x∈dst ev-f₌ = ev-f₌
  -- impossible cases
  Fww[$⇒] {event-init _ _ _}         x∈dst ()
  Fww[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fww[$⇒] {event-skip _ _}           x∈dst ()
  Fww[$⇒] {event _ _ (lab-f F-ld)}   x∈dst ()
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₁ _
  Fww[$⇒] {event _ _ (lab-f F-full)} x∈dst () | inj₂ _

  Fww[⇒] : Pred[⇒] (LIMM.EvF₌ WW) (Armv8.EvF₌ F-st)
  Fww[⇒] = [$⇒]→₁[⇒] Fww[$⇒]


  Fsc[$⇒] : Pred[$⇒] (LIMM.EvF₌ SC) (Armv8.EvF₌ F-full)
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst _ with ⇔₁-apply-⊆₁ org-f-def (x∈dst , ev-f₌)
  Fsc[$⇒] {event _ _ (lab-f F-full)} x∈dst ev-f₌ | inj₂ _ = ev-f₌
  -- impossible cases
  Fsc[$⇒] {event-init _ _ _}         x∈dst ()
  Fsc[$⇒] {event _ _ (lab-a _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event _ _ (lab-q _ _)}    x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event _ _ (lab-l _ _ _)}  x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event _ _ lab-isb}        x∈dst _ = ⊥-elim (¬ev-bound dst-ok x∈dst (λ()))
  Fsc[$⇒] {event-skip _ _}           x∈dst ()
  Fsc[$⇒] {event _ _ (lab-f F-ld)}   x∈dst ()

  Fsc[⇒] : Pred[⇒] (LIMM.EvF₌ SC) (Armv8.EvF₌ F-full)
  Fsc[⇒] = [$⇒]→₁[⇒] Fsc[$⇒]
