{-# OPTIONS --safe #-}


open import Arch.General.Execution using (Execution)
open import Arch.LIMM using (LabelLIMM)
open import TransformFWAW using (FWAW-Restricted)


module Proof.Elimination.FWAW.Execution
  (dst : Execution LabelLIMM)
  (dst-ok : FWAW-Restricted dst)
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
import Proof.Framework LabelLIMM dst (FWAW-Restricted.wf dst-ok) as Ψ
import Proof.Elimination.Framework dst (FWAW-Restricted.wf dst-ok) as Δ


open Ex.Execution
open Ex.WellFormed
open TransformFWAW.Extra dst-ok
open FWAW-Restricted dst-ok


dst-wf = wf


--
-- The transformation:
--
-- WAW: X = v'; X = v  ↦  X = v
--      ^
--      |
--     This Write becomes a Skip
--


-- File structure
-- * General Proof Framework
-- * Elimination Proof Framework
-- * Execution
-- * Extra


-- # Backward Mapping of Execution

ev[⇐] : {x : Event LabelLIMM} → (x∈dst : x ∈ events dst) → Event LabelLIMM
ev[⇐] x@{event-init _ _ _} x∈dst = x
ev[⇐] {event-skip uid tid} x∈dst with ℕ-dec uid elim-uid
... | yes refl     = event uid tid (lab-w tmov elim-loc elim-val)
... | no  uid≢elim = event-skip uid tid
ev[⇐] x@{event _ _ _} x∈dst = x
  
elim-wₙₜ : EvWₙₜ tmov (ev[⇐] elim∈ex)
elim-wₙₜ with inspect elim-ev-skip
elim-wₙₜ | ev-skip with≡ refl with ℕ-dec elim-uid elim-uid
elim-wₙₜ | ev-skip with≡ refl | yes refl      = ev-w is-w refl
elim-wₙₜ | ev-skip with≡ refl | no ¬elim-elim = ⊥-elim (¬elim-elim refl)


-- # Framework

open Ψ.Definitions ev[⇐]
open Δ.Types ev[⇐] elim-ev

src-po : Rel (Event LabelLIMM) ℓzero
src-po = src-rel (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

-- Note that `co` is an order, and thus transitive. The order between other `co`-related events remains preserved.
--
-- We add additional edges, though:
-- * co[py] → co[ey]
-- * co[xp] → co[xe] if x ≢ e
data SrcCo (x y : Event LabelLIMM) : Set where
  co-dst : src-rel (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) x y → SrcCo x y
  -- co[py] → co[ey]
  co-newˡ : {y-dst : Event LabelLIMM}
    → (dst-co[py] : co dst pres₂-ev y-dst)
    → x ≡ ev[⇐] elim∈ex
    → y ≡ ev[⇐] (coʳ∈ex dst-wf dst-co[py])
    → SrcCo x y
  -- co[xp] → co[xe]
  co-newʳ : {x-dst : Event LabelLIMM}
    → (dst-co[xp] : co dst x-dst pres₂-ev)
    → x ≡ ev[⇐] (coˡ∈ex dst-wf dst-co[xp])
    → y ≡ ev[⇐] elim∈ex
    → SrcCo x y
  co-ep :
      x ≡ ev[⇐] elim∈ex
    → y ≡ ev[⇐] pres₂∈ex
    → SrcCo x y

src-rf : Rel (Event LabelLIMM) ℓzero
-- There is no need to re-attach the source read of a preserved write to it's preceding eliminated write
-- as we're picking the execution. An eliminated write is never read from.
src-rf = src-rel (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

elim-rwₙₜ : EvRWₙₜ tmov (ev[⇐] elim∈ex)
elim-rwₙₜ = wₙₜ⇒rwₙₜ elim-wₙₜ

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
loc[$⇒] {_} {event-skip _ _}   ¬elim-x x∈dst (has-loc-w is-w refl) | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid , elim∈ex)))
loc[$⇒] {_} {event _ _ _}      ¬elim-x x∈dst x-loc = x-loc

val[$⇒] : {val : Value} → CPred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _} ¬elim-x x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-skip uid _} ¬elim-x x∈dst _ with ℕ-dec uid elim-uid
val[$⇒] {_} {event-skip _ _}   ¬elim-x x∈dst (has-val-w is-w refl) | yes refl =
  ⊥-elim (¬elim-x (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid , elim∈ex)))
val[$⇒] {_} {event _ _ _}      ¬elim-x x∈dst x-val = x-val

Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-skip uid _} x∈dst _           with ℕ-dec uid elim-uid
Rₜ[$⇒] {_} {event-skip _ _}   x∈dst (ev-r () _) | yes refl
Rₜ[$⇒] {_} {event _ _ _}      x∈dst (ev-r is-r refl) = ev-r is-r refl

Wₐ[$⇒] : Pred[$⇒]² (EvWₜ trmw)
Wₐ[$⇒] {event-init _ _ _} x∈dst (ev-init ())
Wₐ[$⇒] {event-skip uid _} x∈dst q with ℕ-dec uid elim-uid
Wₐ[$⇒] {event-skip _ _}   x∈dst (ev-w is-w ()) | yes refl
Wₐ[$⇒] {event _ _ _}      x∈dst (ev-w is-w refl) = ev-w is-w refl

Wᵣ[$⇒] : CPred[$⇒]² (EvWₜ tmov)
Wᵣ[$⇒] {event-init _ _ _} ¬x-elim x∈dst (ev-init refl) = ev-init refl
Wᵣ[$⇒] {event-skip uid _} ¬x-elim x∈dst _ with ℕ-dec uid elim-uid
Wᵣ[$⇒] {event-skip _ _}   ¬x-elim x∈dst _ | yes refl =
  ⊥-elim (¬x-elim (unique-ids dst-wf _ (has-uid-skip , x∈dst) (elim-has-uid , elim∈ex)))
Wᵣ[$⇒] {event _ _ _} ¬x-elim x∈dst (ev-w is-w refl) = ev-w is-w refl


co[$⇒] : CRel[$⇒] SrcCo (co dst)
co[$⇒] ¬x-elim ¬y-elim x∈dst y∈dst (co-dst dst-co[xy]) =
  rel[$⇒] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) x∈dst y∈dst dst-co[xy]
co[$⇒] ¬x-elim ¬y-elim x∈dst y∈dst (co-newˡ dst-co[py] p _) = ⊥-elim (¬x-elim (ev[$⇒]eq x∈dst elim∈ex p))
co[$⇒] ¬x-elim ¬y-elim x∈dst y∈dst (co-newʳ dst-co[xp] _ q) = ⊥-elim (¬y-elim (ev[$⇒]eq y∈dst elim∈ex q))
co[$⇒] ¬x-elim ¬y-elim x∈dst y∈dst (co-ep p _) = ⊥-elim (¬x-elim (ev[$⇒]eq x∈dst elim∈ex p))

co[⇐] : Rel[⇐] SrcCo (co dst)
co[⇐] x∈dst y∈dst = co-dst ∘ rel[⇐] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) x∈dst y∈dst


rf[$⇒] : Rel[$⇒] src-rf (rf dst)
rf[$⇒] = rel[$⇒] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

rf[⇐] : Rel[⇐] src-rf (rf dst)
rf[⇐] = rel[⇐] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

δ : Δ.EliminationFramework
δ =
  record
    { ψ        = ψ
    ; elim-ev  = elim-ev
    ; elim∈ex  = elim∈ex
    ; src-co   = SrcCo
    ; src-rf   = src-rf
    ; elim-r/w = elim-rwₙₜ
    ; loc[⇐]   = loc[⇐]
    ; val[⇐]   = val[⇐]
    ; Wₜ[⇐]    = Wₜ[⇐]
    ; Rₜ[⇐]    = Rₜ[⇐]
    ; F₌[⇐]    = F₌[⇐]
    ; F₌[$⇒]   = F₌[$⇒]
    ; Wₐ[$⇒]   = Wₐ[$⇒]
    ; Rₐ[$⇒]   = Rₜ[$⇒]
    ; rf[⇐]    = rf[⇐]
    ; co[⇐]    = co[⇐]
    ; Wᵣ[$⇒]   = Wᵣ[$⇒]
    ; Rᵣ[$⇒]   = λ _ → Rₜ[$⇒]
    ; loc[$⇒]  = loc[$⇒]
    ; val[$⇒]  = val[$⇒]
    ; rf[$⇒]   = λ _ _ → rf[$⇒]
    ; co[$⇒]   = co[$⇒]
    }


open Δ.Definitions δ


-- # Extra Helpers

module Extra where

  src-pres₁-ev : Event LabelLIMM
  src-pres₁-ev = pres₁-ev

  src-pres₂-ev : Event LabelLIMM
  src-pres₂-ev = pres₂-ev

  src-elim-def : src-elim-ev ≡ ev[⇐] elim∈ex
  src-elim-def = refl

  -- | The preserved event is identical between the source and target
  src-pres₁-def : src-pres₁-ev ≡ ev[⇐] pres₁∈ex
  src-pres₁-def with pres₁-f
  ... | ev-f is-f = refl
  
  -- | The preserved event is identical between the source and target
  src-pres₂-def : src-pres₂-ev ≡ ev[⇐] pres₂∈ex
  src-pres₂-def with pres₂-wₙᵣ
  ... | ev-w is-w refl = refl
  
  pres₁-f₌ : EvF₌ WW pres₁-ev
  pres₁-f₌ =
    let (z , z-ww , pi[zp₂]) = po-w-ww pres₂∈ex pres₂-wₙᵣ
        z≡p₁ = po-immˡ wf pi[zp₂] pi[p₁p₂]ᵗ
    in subst (EvF₌ WW) z≡p₁ z-ww
  
  pres₁∈src : src-pres₁-ev ∈ events src
  pres₁∈src with pres₁-f
  ... | ev-f is-f = _ , pres₁∈ex , refl

  pres₂∈src : src-pres₂-ev ∈ events src
  pres₂∈src with pres₂-wₙᵣ
  ... | ev-w is-w refl = _ , pres₂∈ex , refl

  elim∈src : src-elim-ev ∈ events src
  elim∈src = events[⇐] elim∈ex

  src-pres₁-f₌ : EvF₌ WW src-pres₁-ev
  src-pres₁-f₌ = subst (EvF₌ WW) (≡-sym src-pres₁-def) (F₌[⇐] pres₁∈ex pres₁-f₌)

  src-pres₂-wᵣ : EvWᵣ src-pres₂-ev
  src-pres₂-wᵣ = subst EvWᵣ (≡-sym src-pres₂-def) (Wₜ[⇐] pres₂∈ex pres₂-wᵣ)

  src-pres₂-w : EvW src-pres₂-ev
  src-pres₂-w = wₜ⇒w src-pres₂-wᵣ
  
  src-elim-w : EvW src-elim-ev
  src-elim-w with elim-ev-skip
  ... | ev-skip with ℕ-dec elim-uid elim-uid
  ... | yes refl = ev-w is-w
  ... | no uid≢uid = ⊥-elim (uid≢uid refl)
  
  src-rfˡ-w : {x y : Event LabelLIMM} → src-rf x y → EvW x
  src-rfˡ-w (x-dst , y-dst , rf[xy] , refl , refl) =
    W[⇐] (rfˡ∈ex dst-wf rf[xy]) (×₂-applyˡ (rf-w×r dst-wf) rf[xy])

  src-rfʳ-r : {x y : Event LabelLIMM} → src-rf x y → EvR y
  src-rfʳ-r (x-dst , y-dst , rf[xy] , refl , refl) =
    R[⇐] (rfʳ∈ex dst-wf rf[xy]) (×₂-applyʳ (rf-w×r dst-wf) rf[xy])

  src-coˡ-w : {x y : Event LabelLIMM} → SrcCo x y → EvW x
  src-coˡ-w (co-dst (_ , _ , co[xy] , refl , refl)) =
    W[⇐] (coˡ∈ex dst-wf co[xy]) (×₂-applyˡ (co-w×w dst-wf) co[xy])
  src-coˡ-w (co-newˡ co[py] refl refl) = wₙₜ⇒w elim-wₙₜ
  src-coˡ-w (co-newʳ co[xp] refl refl) =
    W[⇐] (coˡ∈ex dst-wf co[xp]) (×₂-applyˡ (co-w×w dst-wf) co[xp])
  src-coˡ-w (co-ep refl refl) = wₙₜ⇒w elim-wₙₜ

  src-coʳ-w : {x y : Event LabelLIMM} → SrcCo x y → EvW y
  src-coʳ-w (co-dst (_ , _ , co[xy] , refl , refl)) =
    W[⇐] (coʳ∈ex dst-wf co[xy]) (×₂-applyʳ (co-w×w dst-wf) co[xy])
  src-coʳ-w (co-newˡ co[py] refl refl) =
    W[⇐] (coʳ∈ex dst-wf co[py]) (×₂-applyʳ (co-w×w dst-wf) co[py])
  src-coʳ-w (co-newʳ co[xp] refl refl) = wₙₜ⇒w elim-wₙₜ
  src-coʳ-w (co-ep refl refl) = subst EvW src-pres₂-def src-pres₂-w


  -- # Eliminated / Preserved Event Definitions

  src-elim-has-uid : HasUid elim-uid src-elim-ev
  src-elim-has-uid = uid[⇐] elim∈ex elim-has-uid

  pi[ep₁] : po-imm src src-elim-ev src-pres₁-ev
  pi[ep₁] =
    subst-rel
      (po-imm src)
      (≡-sym src-elim-def)
      (≡-sym src-pres₁-def)
      (pi[⇐] elim∈ex pres₁∈ex pi[ep₁]ᵗ)

  pi[p₁p₂] : po-imm src src-pres₁-ev src-pres₂-ev
  pi[p₁p₂] =
    subst-rel
      (po-imm src)
      (≡-sym src-pres₁-def)
      (≡-sym src-pres₂-def)
      (pi[⇐] pres₁∈ex pres₂∈ex pi[p₁p₂]ᵗ)

  po[ep₂] : po src src-elim-ev src-pres₂-ev
  po[ep₂] =
    subst-rel
      (po src)
      (≡-sym src-elim-def)
      (≡-sym src-pres₂-def)
      (po[⇐] elim∈ex pres₂∈ex po[ep₂]ᵗ)

  src-elim-has-loc : HasLoc elim-loc src-elim-ev
  src-elim-has-loc with elim-ev-skip
  src-elim-has-loc | ev-skip with ℕ-dec elim-uid elim-uid
  src-elim-has-loc | ev-skip | yes refl = has-loc-w is-w refl
  src-elim-has-loc | ev-skip | no ¬elim-elim = ⊥-elim (¬elim-elim refl)

  src-elim-has-val : HasVal elim-val src-elim-ev
  src-elim-has-val with elim-ev-skip
  src-elim-has-val | ev-skip with ℕ-dec elim-uid elim-uid
  src-elim-has-val | ev-skip | yes refl = has-val-w is-w refl
  src-elim-has-val | ev-skip | no ¬elim-elim = ⊥-elim (¬elim-elim refl)

  src-pres₂-has-loc : HasLoc elim-loc src-pres₂-ev
  src-pres₂-has-loc =
    subst
      (HasLoc elim-loc)
      (≡-sym src-pres₂-def)
      (loc[⇐] pres₂∈ex pres₂-has-loc)
  
  src-pres₂-has-val : HasVal elim-val src-pres₂-ev
  src-pres₂-has-val =
    subst
      (HasVal elim-val)
      (≡-sym src-pres₂-def)
      (val[⇐] pres₂∈ex pres₂-has-val)

  ep₂-sloc : SameLoc src-elim-ev src-pres₂-ev
  ep₂-sloc = same-loc src-elim-has-loc src-pres₂-has-loc

  ep₂-sval : SameVal src-elim-ev src-pres₂-ev
  ep₂-sval = same-val src-elim-has-val src-pres₂-has-val

  ¬pres₁-elim : src-pres₁-ev ≢ src-elim-ev
  ¬pres₁-elim p₁≡e with ev[$⇒]eq pres₁∈ex elim∈ex (≡-trans (≡-sym src-pres₁-def) p₁≡e)
  ... | refl = po-irreflexive dst-wf refl (proj₁ pi[ep₁]ᵗ)

  ¬pres₂-elim : src-pres₂-ev ≢ src-elim-ev
  ¬pres₂-elim p₂≡e with ev[$⇒]eq pres₂∈ex elim∈ex (≡-trans (≡-sym src-pres₂-def) p₂≡e)
  ... | refl = po-irreflexive dst-wf refl po[ep₂]ᵗ
  

  -- # Relation properties

  rfˡ∈src : rf src ˡ∈src
  rfˡ∈src = relˡ∈src (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

  rfʳ∈src : rf src ʳ∈src
  rfʳ∈src = relʳ∈src (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)
  
  udr-rf∈src : udr[ rf src ]∈src
  udr-rf∈src = lr→udr (rf src) rfˡ∈src rfʳ∈src


  coˡ∈src : co src ˡ∈src
  coˡ∈src (co-dst co[xy]) = relˡ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) co[xy]
  coˡ∈src (co-newˡ co[py] refl refl) = elim∈src
  coˡ∈src (co-newʳ co[xp] refl refl) = events[⇐] (coˡ∈ex dst-wf co[xp])
  coˡ∈src (co-ep refl refl) = elim∈src

  coʳ∈src : co src ʳ∈src
  coʳ∈src (co-dst co[xy]) = relʳ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf) co[xy]
  coʳ∈src (co-newˡ co[py] refl refl) = events[⇐] (coʳ∈ex dst-wf co[py])
  coʳ∈src (co-newʳ co[xp] refl refl) = elim∈src
  coʳ∈src (co-ep refl refl) = events[⇐] pres₂∈ex

  udr-co∈src : udr[ co src ]∈src
  udr-co∈src = lr→udr (co src) coˡ∈src coʳ∈src


  coˡ-e⇒p : {y : Event LabelLIMM} → y ≢ src-pres₂-ev → co src src-elim-ev y → co src src-pres₂-ev y
  coˡ-e⇒p ¬y-pres₂ (co-newˡ co[py] refl refl) = co-dst (_ , _ , co[py] , src-pres₂-def , refl)
  -- impossible cases
  coˡ-e⇒p ¬y-pres₂ (co-dst (_ , _ , co[ey] , τ , refl))
    with ev[$⇒]eq elim∈ex (coˡ∈ex dst-wf co[ey]) τ
  ... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyˡ (co-w×w dst-wf) co[ey] , elim-ev-skip))
  coˡ-e⇒p ¬y-pres₂ (co-newʳ co[xp] τ refl)
    with ev[$⇒]eq elim∈ex (coˡ∈ex dst-wf co[xp]) τ
  ... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyˡ (co-w×w dst-wf) co[xp] , elim-ev-skip))
  coˡ-e⇒p ¬y-pres₂ (co-ep refl refl) = ⊥-elim (¬y-pres₂ (≡-sym src-pres₂-def))


  coʳ-e⇒p : {x : Event LabelLIMM} → co src x src-elim-ev → co src x src-pres₂-ev
  coʳ-e⇒p (co-dst (_ , _ , co[xe] , refl , τ))
    with ev[$⇒]eq elim∈ex (coʳ∈ex dst-wf co[xe]) τ
  ... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyʳ (co-w×w dst-wf) co[xe] , elim-ev-skip))
  coʳ-e⇒p (co-newˡ co[pe] refl τ)
    with ev[$⇒]eq elim∈ex (coʳ∈ex dst-wf co[pe]) τ
  ... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyʳ (co-w×w dst-wf) co[pe] , elim-ev-skip))
  coʳ-e⇒p (co-newʳ dst-co[xp] refl refl) = co-dst (_ , _ , dst-co[xp] , refl , src-pres₂-def)
  coʳ-e⇒p (co-ep refl τ) = ⊥-elim (¬pres₂-elim (≡-trans src-pres₂-def (≡-sym τ)))


  frʳ-e⇒p : ∀ {x : Event LabelLIMM} → fr src x src-elim-ev → fr src x src-pres₂-ev
  frʳ-e⇒p (rf⁻¹[xz] ⨾[ _ ]⨾ co[ze]) = rf⁻¹[xz] ⨾[ _ ]⨾ coʳ-e⇒p co[ze]
