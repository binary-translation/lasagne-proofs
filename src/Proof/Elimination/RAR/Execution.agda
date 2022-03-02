{-# OPTIONS --safe #-}


open import Arch.General.Execution using (Execution)
open import Arch.LIMM using (LabelLIMM)
open import TransformRAR using (RAR-Restricted)


module Proof.Elimination.RAR.Execution
  (dst : Execution LabelLIMM)
  (dst-ok : RAR-Restricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using () renaming (zero to ℓzero)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; Transitive; Trichotomous; tri<; tri≈; tri>)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.LIMM as LIMM
-- Local imports: Proof Components
import Proof.Framework LabelLIMM dst (RAR-Restricted.wf dst-ok) as Ψ
import Proof.Elimination.Framework dst (RAR-Restricted.wf dst-ok) as Δ


open Ex.Execution
open Ex.WellFormed
open TransformRAR.Extra dst-ok
open RAR-Restricted dst-ok


dst-wf = wf


--
-- The transformation:
--
-- a = X; b = X  ->  a = X; b = a
--


-- File structure
-- * General Proof Framework
-- * Elimination Proof Framework
-- * Execution
-- * Extra


-- # General Definitions

-- | It is identical between the source and target, because it is preserved.
src-preserved-ev : Event LabelLIMM
src-preserved-ev = preserved-ev


-- # Backward Mapping of Execution

ev[⇐] : {x : Event LabelLIMM} → (x∈dst : x ∈ events dst) → Event LabelLIMM
ev[⇐] x@{event-init _ _ _} x∈dst = x
-- Note that the target execution only /has a single skip/, which is obtained from the elimination.
ev[⇐] {event-skip uid tid} x∈dst with ℕ-dec uid elim-uid
... | yes refl     = event uid tid (lab-r tmov elim-loc elim-val)
... | no  uid≢elim = event-skip uid tid
ev[⇐] x@{event _ _ _} x∈dst = x
  
elim-rₜ : EvRₜ tmov (ev[⇐] elim∈ex)
elim-rₜ with inspect elim-ev-skip
elim-rₜ | ev-skip with≡ refl with ℕ-dec elim-uid elim-uid
elim-rₜ | ev-skip with≡ refl | yes refl      = ev-r is-r refl
elim-rₜ | ev-skip with≡ refl | no ¬elim-elim = ⊥-elim (¬elim-elim refl)


-- # Framework

open Ψ.Definitions ev[⇐]
open Δ.Types ev[⇐] elim-ev

src-po : Rel (Event LabelLIMM) ℓzero
src-po = src-rel (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

src-co : Rel (Event LabelLIMM) ℓzero
src-co = src-rel (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

-- W × R
data SrcRf (x y : Event LabelLIMM) : Set where
  rf-dst : src-rel (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf) x y → SrcRf x y
  -- the eliminated event reads from whatever the preserved event reads from
  rf-new : {x-dst : Event LabelLIMM}
      (dst-rf[xy] : rf dst x-dst preserved-ev)
    → x ≡ ev[⇐] (rfˡ∈ex dst-wf dst-rf[xy])
    → y ≡ ev[⇐] elim∈ex
    → SrcRf x y
    

elim-rwₙₜ : EvRWₙₜ tmov (ev[⇐] elim∈ex)
elim-rwₙₜ = rₜ⇒rwₙₜ elim-rₜ

uid[⇐] : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
uid[⇐]       x∈dst has-uid-init = has-uid-init
uid[⇐] {uid} x∈dst has-uid-skip with ℕ-dec uid elim-uid
uid[⇐]       x∈dst has-uid-skip | yes refl = has-uid
uid[⇐]       x∈dst has-uid-skip | no  _    = has-uid-skip
uid[⇐]       x∈dst has-uid = has-uid

uid[$⇒] : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _} x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip uid _} x∈dst _ with ℕ-dec uid elim-uid
uid[$⇒] {_}                    x∈dst has-uid      | yes refl = has-uid-skip
uid[$⇒] {_}                    x∈dst has-uid-skip | no  _    = has-uid-skip
uid[$⇒] {_} {event _ _ _}      x∈dst has-uid = has-uid


tid[⇐] : {tid : ThreadId} → Pred[⇐]² (HasTid tid)
tid[⇐] {_} {event-skip uid _} x∈dst has-tid-skip with ℕ-dec uid elim-uid
tid[⇐] {_}                    x∈dst has-tid-skip | yes refl = has-tid
tid[⇐] {_}                    x∈dst has-tid-skip | no  _    = has-tid-skip
tid[⇐] {_}                    x∈dst has-tid = has-tid

tid[$⇒] : {tid : ThreadId} → Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip uid _} x∈dst _ with ℕ-dec uid elim-uid
tid[$⇒] {_}                    x∈dst has-tid      | yes refl    = has-tid-skip
tid[$⇒] {_}                    x∈dst has-tid-skip | no tid≢elim = has-tid-skip
tid[$⇒] {_} {event _ _ _}      x∈dst has-tid = has-tid


loc[⇐] : {loc : Location} → Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init          = has-loc-init
loc[⇐] x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[⇐] x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl

val[⇐] : {val : Value} → Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init          = has-val-init
val[⇐] x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[⇐] x∈dst (has-val-w is-w refl) = has-val-w is-w refl


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init

Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _} x∈dst ev-init = ev-init
Init[$⇒] {event-skip uid _} x∈dst _ with ℕ-dec uid elim-uid
Init[$⇒]                    x∈dst () | yes refl


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


-- # Elimination-specific Framework

open Ψ.WellFormed ψ

Wₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] x∈dst (ev-init refl)   = ev-init refl
Wₜ[⇐] x∈dst (ev-w is-w refl) = ev-w is-w refl

Rₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] x∈dst (ev-r is-r refl) = ev-r is-r refl


F₌[⇐] : {m : F-mode} → Pred[⇐] (EvF₌ m) (EvF₌ m)
F₌[⇐] x∈dst ev-f₌ = ev-f₌

F₌[$⇒] : {m : F-mode} → Pred[$⇒] (EvF₌ m) (EvF₌ m)
F₌[$⇒] {_} {event-skip uid _} x∈dst _ with ℕ-dec uid elim-uid
F₌[$⇒] {_} {event-skip _   _} x∈dst () | yes refl
F₌[$⇒] {_} {event _ _ _}      x∈dst ev-f₌ = ev-f₌


-- Conditionally preserved properties

loc[$⇒] : {loc : Location} → CPred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _} ¬elim-x x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-skip uid _} ¬elim-x x∈dst _ with ℕ-dec uid elim-uid
loc[$⇒] {_} {event-skip _ _}   ¬elim-x x∈dst (has-loc-r is-r refl) | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid , elim∈ex)))
loc[$⇒] {_} {event _ _ _}      ¬elim-x x∈dst x-loc = x-loc

val[$⇒] : {val : Value} → CPred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _} ¬elim-x x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-skip uid _} ¬elim-x x∈dst _ with ℕ-dec uid elim-uid
val[$⇒] {_} {event-skip _ _}   ¬elim-x x∈dst (has-val-r is-r refl) | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid , elim∈ex)))
val[$⇒] {_} {event _ _ _}      ¬elim-x x∈dst x-val = x-val

Wₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _} x∈dst (ev-init refl) = ev-init refl
Wₜ[$⇒] {_} {event-skip uid _} x∈dst _           with ℕ-dec uid elim-uid
Wₜ[$⇒] {_} {event-skip _ _}   x∈dst (ev-w () _) | yes refl
Wₜ[$⇒] {_} {event _ _ _}      x∈dst (ev-w is-w refl) = ev-w is-w refl

Rₐ[$⇒] : Pred[$⇒]² (EvRₜ trmw)
Rₐ[$⇒] {event-skip uid _} x∈dst q with ℕ-dec uid elim-uid
Rₐ[$⇒] {event-skip _ _}   x∈dst (ev-r is-r ()) | yes refl
Rₐ[$⇒] {event _ _ _}      x∈dst (ev-r is-r refl) = ev-r is-r refl

Rᵣ[$⇒] : CPred[$⇒]² (EvRₜ tmov)
Rᵣ[$⇒] {event-skip uid _} ¬elim-x x∈dst _ with ℕ-dec uid elim-uid
Rᵣ[$⇒] {event-skip _ _}   ¬elim-x x∈dst q | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid , elim∈ex)))
Rᵣ[$⇒] {event _ _ _}      ¬elim-x x∈dst (ev-r is-r refl) = ev-r is-r refl


co[$⇒] : Rel[$⇒] src-co (co dst)
co[$⇒] = rel[$⇒] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

co[⇐] : Rel[⇐] src-co (co dst)
co[⇐] = rel[⇐] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)


rf[$⇒] : CRel[$⇒] SrcRf (rf dst)
rf[$⇒] _ _ x∈dst y∈dst (rf-dst dst-rf[xy]) =
  rel[$⇒] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf) x∈dst y∈dst dst-rf[xy]
rf[$⇒] _ ¬y-elim x∈dst y∈dst (rf-new dst-rf[xy] p q) =
  ⊥-elim (¬y-elim (ev[$⇒]eq y∈dst elim∈ex q))

rf[⇐] : Rel[⇐] SrcRf (rf dst)
rf[⇐] x∈dst y∈dst = rf-dst ∘ (rel[⇐] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf) x∈dst y∈dst)

δ : Δ.EliminationFramework
δ =
  record
    { ψ        = ψ
    ; elim-ev  = elim-ev
    ; elim∈ex  = elim∈ex
    ; src-co   = src-co
    ; src-rf   = SrcRf
    ; elim-r/w = elim-rwₙₜ
    ; loc[⇐]   = loc[⇐]
    ; val[⇐]   = val[⇐]
    ; Wₜ[⇐]    = Wₜ[⇐]
    ; Rₜ[⇐]    = Rₜ[⇐]
    ; F₌[⇐]    = F₌[⇐]
    ; F₌[$⇒]   = F₌[$⇒]
    ; Wₐ[$⇒]   = Wₜ[$⇒]
    ; Rₐ[$⇒]   = Rₐ[$⇒]
    ; rf[⇐]    = rf[⇐]
    ; co[⇐]    = co[⇐]
    ; Wᵣ[$⇒]   = λ _ → Wₜ[$⇒]
    ; Rᵣ[$⇒]   = Rᵣ[$⇒]
    ; loc[$⇒]  = loc[$⇒]
    ; val[$⇒]  = val[$⇒]
    ; rf[$⇒]   = rf[$⇒]
    ; co[$⇒]   = λ _ _ → co[$⇒]
    }


open Δ.Definitions δ


-- # Extra Helpers

module Extra where
  
  elim-¬w : {x : Event LabelLIMM} → EvW x → x ≢ src-elim-ev
  elim-¬w x-w refl = disjoint-r/w _ (rₜ⇒r elim-rₜ , x-w)
  
  src-rfˡ-w : {x y : Event LabelLIMM} → SrcRf x y → EvW x
  src-rfˡ-w (rf-dst (_ , _ , dst-rf[xy] , refl , refl)) =
    W[⇐] (rfˡ∈ex dst-wf dst-rf[xy]) (×₂-applyˡ (rf-w×r dst-wf) dst-rf[xy])
  src-rfˡ-w (rf-new dst-rf[xy] refl refl) =
    W[⇐] (rfˡ∈ex dst-wf dst-rf[xy]) (×₂-applyˡ (rf-w×r dst-wf) dst-rf[xy])

  src-rfʳ-r : {x y : Event LabelLIMM} → SrcRf x y → EvR y
  src-rfʳ-r (rf-dst (_ , _ , dst-rf[xy] , refl , refl)) =
    R[⇐] (rfʳ∈ex dst-wf dst-rf[xy]) (×₂-applyʳ (rf-w×r dst-wf) dst-rf[xy])
  src-rfʳ-r (rf-new dst-rf[xy] refl refl) = rₜ⇒r elim-rₜ

  src-coˡ-w : {x y : Event LabelLIMM} → co src x y → EvW x
  src-coˡ-w (x-dst , y-dst , dst-co[xy] , refl , refl) =
    W[⇐] (coˡ∈ex dst-wf dst-co[xy]) (×₂-applyˡ (co-w×w dst-wf) dst-co[xy])

  src-coʳ-w : {x y : Event LabelLIMM} → co src x y → EvW y
  src-coʳ-w (x-dst , y-dst , dst-co[xy] , refl , refl) =
    W[⇐] (coʳ∈ex dst-wf dst-co[xy]) (×₂-applyʳ (co-w×w dst-wf) dst-co[xy])


  -- # Eliminated / Preserved Event Definitions

  src-preserved-def : src-preserved-ev ≡ ev[⇐] preserved∈ex
  src-preserved-def with preserved-ev-r
  ... | ev-r is-r refl = refl

  elim∈src : src-elim-ev ∈ events src
  elim∈src = events[⇐] elim∈ex

  preserved∈src : src-preserved-ev ∈ events src
  preserved∈src = subst (events src) (≡-sym src-preserved-def) (events[⇐] preserved∈ex)

  src-elim-has-uid : HasUid elim-uid src-elim-ev
  src-elim-has-uid = uid[⇐] elim∈ex (elim-has-uid)

  src-transform-pair : po-imm src src-preserved-ev src-elim-ev
  src-transform-pair =
    subst-rel (po-imm src)
      (≡-sym src-preserved-def)
      refl
      (pi[⇐$] (events[⇐] preserved∈ex) (events[⇐] elim∈ex) transform-pair)

  src-elim-has-loc : HasLoc elim-loc src-elim-ev
  src-elim-has-loc with inspect elim-ev-skip
  src-elim-has-loc | ev-skip with≡ refl with ℕ-dec elim-uid elim-uid
  src-elim-has-loc | ev-skip with≡ refl | yes refl = has-loc-r is-r refl
  src-elim-has-loc | ev-skip with≡ refl | no ¬elim-elim = ⊥-elim (¬elim-elim refl)

  src-elim-has-val : HasVal elim-val src-elim-ev
  src-elim-has-val with inspect elim-ev-skip
  src-elim-has-val | ev-skip with≡ refl with ℕ-dec elim-uid elim-uid
  src-elim-has-val | ev-skip with≡ refl | yes refl = has-val-r is-r refl
  src-elim-has-val | ev-skip with≡ refl | no ¬elim-elim = ⊥-elim (¬elim-elim refl)

  pe-sloc : SameLoc src-preserved-ev src-elim-ev
  pe-sloc = same-loc preserved-has-loc src-elim-has-loc

  pe-sval : SameVal src-preserved-ev src-elim-ev
  pe-sval = same-val preserved-has-val src-elim-has-val

  ¬elim-pres-dst : preserved-ev ≢ elim-ev
  ¬elim-pres-dst refl = po-irreflexive dst-wf refl (proj₁ transform-pair)

  ¬elim-pres-src : src-preserved-ev ≢ src-elim-ev
  ¬elim-pres-src q =
    let p≡e = ev[$⇒]eq preserved∈ex elim∈ex (≡-trans (≡-sym src-preserved-def) q)
    in ¬elim-pres-dst p≡e


  -- # Relation properties

  rfˡ∈src : rf src ˡ∈src
  rfˡ∈src (rf-dst src-rf[xy]) = relˡ∈src (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf) src-rf[xy]
  rfˡ∈src (rf-new dst-rf[xy] refl refl) = events[⇐] (rfˡ∈ex dst-wf dst-rf[xy])

  rfʳ∈src : rf src ʳ∈src
  rfʳ∈src (rf-dst (_ , _ , dst-rf[xy] , refl , refl)) = events[⇐] (rfʳ∈ex dst-wf dst-rf[xy])
  rfʳ∈src (rf-new dst-rf[xy] refl refl) = elim∈src

  udr-rf∈src : udr[ rf src ]∈src
  udr-rf∈src = lr→udr (rf src) rfˡ∈src rfʳ∈src


  coˡ∈src : co src ˡ∈src
  coˡ∈src = relˡ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

  coʳ∈src : co src ʳ∈src
  coʳ∈src = relʳ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

  udr-co∈src : udr[ co src ]∈src
  udr-co∈src = lr→udr (co src) coˡ∈src coʳ∈src


  rfʳ-e⇒p : ∀ {x : Event LabelLIMM} → rf src x src-elim-ev → rf src x src-preserved-ev
  rfʳ-e⇒p (rf-dst (_ , _ , dst-rf[xy] , refl , q)) with ev[$⇒]eq elim∈ex (rfʳ∈ex dst-wf dst-rf[xy]) q
  ... | refl = ⊥-elim (disjoint-r/skip _ (×₂-applyʳ (rf-w×r dst-wf) dst-rf[xy] , elim-ev-skip))
  rfʳ-e⇒p (rf-new dst-rf[xy] refl refl) =
    rf-dst (_ , _ , dst-rf[xy] , refl , ≡-trans src-preserved-def (ev[⇐]eq preserved∈ex (rfʳ∈ex dst-wf dst-rf[xy])))

  frˡ-e⇒p : ∀ {y : Event LabelLIMM} → fr src src-elim-ev y → fr src src-preserved-ev y
  frˡ-e⇒p (rf⁻¹[ez] ⨾[ _ ]⨾ co[zy]) = rfʳ-e⇒p rf⁻¹[ez] ⨾[ _ ]⨾ co[zy]

  fr[⇒] : {x y : Event LabelLIMM}
    → x ≢ src-elim-ev
    → (x∈src : x ∈ src-events) (y∈src : y ∈ src-events)
    → fr src x y
      ----------------------------------
    → fr dst (ev[⇒] x∈src) (ev[⇒] y∈src)
  fr[⇒] ¬elim-x x∈src y∈src (rf⁻¹[xz] ⨾[ _ ]⨾ co[zy]) =
    let z∈src = coˡ∈src co[zy]
        ¬elim-z = elim-¬w (src-rfˡ-w rf⁻¹[xz])
        ¬elim-y = elim-¬w (src-coʳ-w co[zy])
    in (rf[⇒] ¬elim-z ¬elim-x z∈src x∈src rf⁻¹[xz] ⨾[ _ ]⨾ co[⇒] ¬elim-z ¬elim-y z∈src y∈src co[zy])

  fre[⇒] : {x y : Event LabelLIMM}
    → x ≢ src-elim-ev
    → (x∈src : x ∈ events src) (y∈src : y ∈ events src)
    → fre src x y
      -----------------------------------
    → fre dst (ev[⇒] x∈src) (ev[⇒] y∈src)
  fre[⇒] ¬elim-x x∈src y∈src (fr[xy] , ¬po[xy]) = (fr[⇒] ¬elim-x x∈src y∈src fr[xy] , ¬po[⇒] x∈src y∈src ¬po[xy])
