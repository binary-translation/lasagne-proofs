{-# OPTIONS --safe #-}

open import Arch.LIMM using (LabelLIMM)
import Arch.General.Execution as Ex


-- | A general framework for writing /elimination proofs/ on LIMM executions.
--
-- An elimination operation always replaces a single non-atomic Read or Write event by a
-- Skip event.
module Proof.Elimination.Framework
  (dst : Ex.Execution LabelLIMM)
  (dst-wf : Ex.WellFormed dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong)
open import Level using () renaming (zero to ℓzero)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Rel; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architecture Definitons
open import Arch.General.Event
open import Arch.General.Execution hiding (WellFormed; Execution)
open import Arch.General.Properties
open import Arch.General.DerivedWellformed
open import Arch.LIMM using (EvF₌; F-mode)
-- Local imports: Proof Components
import Proof.Framework LabelLIMM dst dst-wf as Ψ


open Ex.Execution
open Ex.WellFormed


module Types
  (ev[⇐] : {x : Event LabelLIMM} → (x∈dst : x ∈ events dst) → Event LabelLIMM)
  (elim-ev : Event LabelLIMM)
  where

  CPred[$⇒] : Pred (Event LabelLIMM) ℓzero → Pred (Event LabelLIMM) ℓzero → Set
  CPred[$⇒] Pˢ Pᵗ = ∀ {x}
    → x ≢ elim-ev
    → (x∈dst : x ∈ events dst)
    → Pˢ (ev[⇐] x∈dst)
    → Pᵗ x
  
  CRel[$⇒] : Rel (Event LabelLIMM) ℓzero → Rel (Event LabelLIMM) ℓzero → Set
  CRel[$⇒] Rˢ Rᵗ = ∀ {x y}
    → x ≢ elim-ev → y ≢ elim-ev
    → (x∈dst : x ∈ events dst) (y∈dst : y ∈ events dst)
    → Rˢ (ev[⇐] x∈dst) (ev[⇐] y∈dst)
    → Rᵗ x y
  
  CPred[$⇒]² : Pred (Event LabelLIMM) ℓzero → Set
  CPred[$⇒]² P = CPred[$⇒] P P
  
  CPred[⇐] : Pred (Event LabelLIMM) ℓzero → Pred (Event LabelLIMM) ℓzero → Set
  CPred[⇐] Pˢ Pᵗ = ∀ {x} → x ≢ elim-ev → (x∈dst : x ∈ events dst) → Pᵗ x → Pˢ (ev[⇐] x∈dst)
  

-- |
record EliminationFramework : Set₁ where
  field
    -- # Definitions
    ψ : Ψ.GeneralFramework
    
    -- | The event (in the target) that is eliminated
    elim-ev  : Event LabelLIMM
    
    elim∈ex  : elim-ev ∈ events dst
    
    src-co   : Rel (Event LabelLIMM) ℓzero
    src-rf   : Rel (Event LabelLIMM) ℓzero

  open Ψ.GeneralFramework ψ using (ev[⇐])
  open Ψ.Definitions ev[⇐] using (Pred[⇐]; Pred[$⇒]; Pred[⇐]²; Pred[$⇒]²; Rel[⇐])
  open Types ev[⇐] elim-ev
  
  field
    -- # Definitions
    
    -- A transformation can only eliminate a /non-atomic/ Read or (non-init) Write instruction
    elim-r/w : EvRWₙₜ tmov (ev[⇐] elim∈ex)


    -- # Properties
    
    loc[⇐]   : {loc : Location} → Pred[⇐]² (HasLoc loc)
    val[⇐]   : {val : Value}    → Pred[⇐]² (HasVal val)
    Wₜ[⇐]    : {tag : Tag}      → Pred[⇐]² (EvWₜ tag)
    Rₜ[⇐]    : {tag : Tag}      → Pred[⇐]² (EvRₜ tag)
    F₌[⇐]    : {m : F-mode}     → Pred[⇐] (EvF₌ m) (EvF₌ m)
    F₌[$⇒]   : {m : F-mode}     → Pred[$⇒] (EvF₌ m) (EvF₌ m)

    -- /atomic/ read/write events
    Wₐ[$⇒] : Pred[$⇒]² (EvWₜ trmw)
    Rₐ[$⇒] : Pred[$⇒]² (EvRₜ trmw)

    rf[⇐] : Rel[⇐] src-rf (rf dst)
    co[⇐] : Rel[⇐] src-co (co dst)

    -- These are conditional on not being eliminated
    
    -- /non-atomic/ read/write events
    Wᵣ[$⇒]   : CPred[$⇒]² (EvWₜ tmov)
    Rᵣ[$⇒]   : CPred[$⇒]² (EvRₜ tmov)
    
    loc[$⇒]  : {loc : Location} → CPred[$⇒]² (HasLoc loc)
    val[$⇒]  : {val : Value} → CPred[$⇒]² (HasVal val)

    rf[$⇒] : CRel[$⇒] src-rf (rf dst)
    co[$⇒] : CRel[$⇒] src-co (co dst)


module Definitions (δ : EliminationFramework) where

  open EliminationFramework δ
  open Ψ.GeneralFramework ψ
  open Ψ.Definitions ev[⇐]
  open Ψ.WellFormed ψ
  open Types ev[⇐] elim-ev
  open import Arch.LIMM.Detour
  

  -- # Execution

  src : Ex.Execution LabelLIMM
  src =
    record {
      events = src-events
    ; po     = src-rel (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)
    ; rf     = src-rf
    ; co     = src-co
    ; rmw    = src-rmw
    }


  poˡ∈src : po src ˡ∈src
  poˡ∈src = relˡ∈src (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)
  
  poʳ∈src : po src ʳ∈src
  poʳ∈src = relʳ∈src (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

  udr-po∈src : udr[ po src ]∈src
  udr-po∈src = lr→udr (po src) poˡ∈src poʳ∈src


  -- # Mapping

  -- ## Mapping: General

  -- | The eliminated event in the source execution
  src-elim-ev : Event LabelLIMM
  src-elim-ev = ev[⇐] elim∈ex


  -- # Mapping: Types

  -- | /Conditional/ forward mapping of predicates.
  -- The mapping holds for any event that is /not the eliminated event/.
  CPred[⇒] : Pred (Event LabelLIMM) ℓzero → Pred (Event LabelLIMM) ℓzero → Set
  CPred[⇒] Pˢ Pᵗ = ∀ {x} → x ≢ src-elim-ev → (x∈src : x ∈ events src) → Pˢ x → Pᵗ (ev[⇒] x∈src)
  
  -- | /Conditional/ forward mapping of relations.
  -- The mapping holds for any event that is /not the eliminated event/.
  CRel[⇒] : Rel (Event LabelLIMM) ℓzero → Rel (Event LabelLIMM) ℓzero → Set
  CRel[⇒] Rˢ Rᵗ = ∀ {x y}
    → x ≢ src-elim-ev → y ≢ src-elim-ev
    → (x∈src : x ∈ events src) (y∈src : y ∈ events src)
    → Rˢ x y → Rᵗ (ev[⇒] x∈src) (ev[⇒] y∈src)
  
  CPred[⇒]² : Pred (Event LabelLIMM) ℓzero → Set
  CPred[⇒]² P = CPred[⇒] P P
  
  CRel[⇒]² : Rel (Event LabelLIMM) ℓzero → Set
  CRel[⇒]² R = CRel[⇒] R R


  -- ## Mapping: Equality

  -- | If a mapped event is the eliminated (skip) event in the target,
  -- then the source event is the eliminated event.
  elim[⇐$]eq : {x : Event LabelLIMM}
    → (x∈src : x ∈ src-events)
    → ev[⇒] x∈src ≡ elim-ev
      ---------------------
    → x ≡ src-elim-ev
  elim[⇐$]eq (_ , elim∈dst , refl) refl =
    cong ev[⇐] (events-unique dst-wf _ elim∈dst elim∈ex)

  -- | If an event in the source is /not/ the eliminated event,
  -- its mapped event is not the eliminated (skip) event.
  elim[⇒]neq : {x : Event LabelLIMM}
    → (x∈src : x ∈ src-events)
    → x ≢ src-elim-ev
      ---------------------
    → ev[⇒] x∈src ≢ elim-ev
  elim[⇒]neq = contrapositive ∘ elim[⇐$]eq

  elim[⇐]neq : {x : Event LabelLIMM}
    → (x∈dst : x ∈ events dst)
    → x ≢ elim-ev
      ---------------------------
    → (ev[⇐] x∈dst) ≢ src-elim-ev
  elim[⇐]neq x∈dst = contrapositive (ev[$⇒]eq x∈dst elim∈ex)


  -- ## Mapping: Converters

  -- | Similar to `[$⇒]→₁[⇒]`, but defined over `CPred[⇒]` instead of `Pred[⇒]`
  [$⇒]→₁[⇒]ᶜ :
      {Pˢ : Pred (Event LabelLIMM) ℓzero}
    → {Pᵗ : Pred (Event LabelLIMM) ℓzero}
    → CPred[$⇒] Pˢ Pᵗ
      ---------------
    → CPred[⇒] Pˢ Pᵗ
  [$⇒]→₁[⇒]ᶜ {Pˢ} P[$⇒] ¬x-elim x∈src =
    P[$⇒] (elim[⇒]neq x∈src ¬x-elim) (events[⇒] x∈src) ∘ subst Pˢ (ev[⇒⇐] x∈src)
    
  -- | Similar to `[$⇒]→₂[⇒]`, but defined over `CRel[⇒]` instead of `Rel[⇒]`
  [$⇒]→₂[⇒]ᶜ :
      {Rˢ : Rel (Event LabelLIMM) ℓzero}
    → {Rᵗ : Rel (Event LabelLIMM) ℓzero}
    → CRel[$⇒] Rˢ Rᵗ
      --------------
    → CRel[⇒] Rˢ Rᵗ
  [$⇒]→₂[⇒]ᶜ {Rˢ} {Rᵗ} R[$⇒] ¬x-elim ¬y-elim x∈src y∈src =
    R[$⇒]
      (elim[⇒]neq x∈src ¬x-elim) (elim[⇒]neq y∈src ¬y-elim)
      (events[⇒] x∈src) (events[⇒] y∈src)
    ∘ subst-rel Rˢ (ev[⇒⇐] x∈src) (ev[⇒⇐] y∈src)


  -- ## Mapping: Predicates

  loc[⇒] : {loc : Location} → CPred[⇒]² (HasLoc loc)
  loc[⇒] = [$⇒]→₁[⇒]ᶜ loc[$⇒]
  
  loc[⇐$] : {loc : Location} → Pred[⇐$]² (HasLoc loc)
  loc[⇐$] = [⇐]→₁[⇐$] loc[⇐]
  
  val[⇒] : {val : Value} → CPred[⇒]² (HasVal val)
  val[⇒] = [$⇒]→₁[⇒]ᶜ val[$⇒]
  
  val[⇐$] : {val : Value} → Pred[⇐$]² (HasVal val)
  val[⇐$] = [⇐]→₁[⇐$] val[⇐]
  

  sloc[⇒] : CRel[⇒]² SameLoc
  sloc[⇒] ¬x-elim ¬y-elim x∈src y∈src (same-loc x-loc y-loc) =
    same-loc (loc[⇒] ¬x-elim x∈src x-loc) (loc[⇒] ¬y-elim y∈src y-loc)

  sloc[⇐$] : Rel[⇐$]² SameLoc
  sloc[⇐$] x∈src y∈src (same-loc x-loc y-loc) =
    same-loc (loc[⇐$] x∈src x-loc) (loc[⇐$] y∈src y-loc)

  sval[⇐$] : Rel[⇐$]² SameVal
  sval[⇐$] x∈src y∈src (same-val x-val y-val) =
    same-val (val[⇐$] x∈src x-val) (val[⇐$] y∈src y-val)


  Wₜ[⇐$] : {tag : Tag} → Pred[⇐$]² (EvWₜ tag)
  Wₜ[⇐$] = [⇐]→₁[⇐$] Wₜ[⇐]
  
  Wₜ[$⇒] : {tag : Tag} → CPred[$⇒]² (EvWₜ tag)
  Wₜ[$⇒] {tmov} ¬x-elim = Wᵣ[$⇒] ¬x-elim
  Wₜ[$⇒] {trmw} ¬x-elim = Wₐ[$⇒]
  
  Wₜ[⇒] : {tag : Tag} → CPred[⇒]² (EvWₜ tag)
  Wₜ[⇒] = [$⇒]→₁[⇒]ᶜ Wₜ[$⇒]

  Wₐ[⇒] : Pred[⇒]² (EvWₜ trmw)
  Wₐ[⇒] = [$⇒]→₁[⇒] Wₐ[$⇒]


  W[⇐] : Pred[⇐]² EvW
  W[⇐] x∈dst = wₜ⇒w ∘ Wₜ[⇐] x∈dst ∘ w⇒wₜ

  W[⇐$] : Pred[⇐$]² EvW
  W[⇐$] = [⇐]→₁[⇐$] W[⇐]
  
  W[⇒] : CPred[⇒]² EvW
  W[⇒] ¬x-elim x∈src = wₜ⇒w ∘ Wₜ[⇒] ¬x-elim x∈src ∘ w⇒wₜ
  
  W[$⇒] : CPred[$⇒]² EvW
  W[$⇒] ¬x-elim x∈dst = wₜ⇒w ∘ Wₜ[$⇒] ¬x-elim x∈dst ∘ w⇒wₜ


  Rₜ[⇐$] : {tag : Tag} → Pred[⇐$]² (EvRₜ tag)
  Rₜ[⇐$] = [⇐]→₁[⇐$] Rₜ[⇐]
  
  Rₜ[$⇒] : {tag : Tag} → CPred[$⇒]² (EvRₜ tag)
  Rₜ[$⇒] {tmov} ¬x-elim = Rᵣ[$⇒] ¬x-elim
  Rₜ[$⇒] {trmw} ¬x-elim = Rₐ[$⇒]
  
  Rₜ[⇒] : {tag : Tag} → CPred[⇒]² (EvRₜ tag)
  Rₜ[⇒] = [$⇒]→₁[⇒]ᶜ Rₜ[$⇒]

  Rₐ[⇒] : Pred[⇒]² (EvRₜ trmw)
  Rₐ[⇒] = [$⇒]→₁[⇒] Rₐ[$⇒]


  R[⇐] : Pred[⇐]² EvR
  R[⇐] x∈dst = rₜ⇒r ∘ Rₜ[⇐] x∈dst ∘ r⇒rₜ
  
  R[⇐$] : Pred[⇐$]² EvR
  R[⇐$] = [⇐]→₁[⇐$] R[⇐]
  
  R[⇒] : CPred[⇒]² EvR
  R[⇒] ¬x-elim x∈src = rₜ⇒r ∘ Rₜ[⇒] ¬x-elim x∈src ∘ r⇒rₜ


  RW[⇒] : CPred[⇒]² EvRW
  RW[⇒] ¬x-elim x∈src x-rw with rw/rw x-rw
  ... | inj₁ x-r = r⇒rw (R[⇒] ¬x-elim x∈src x-r)
  ... | inj₂ x-w = w⇒rw (W[⇒] ¬x-elim x∈src x-w)
  
  F₌[⇒] : {mode : F-mode} → Pred[⇒] (EvF₌ mode) (EvF₌ mode)
  F₌[⇒] = [$⇒]→₁[⇒] F₌[$⇒]
  

  -- ## Mapping: Relations

  -- ### Mapping - Relations: po

  po[⇐] : Rel[⇐] (po src) (po dst)
  po[⇐] = rel[⇐] (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

  po[⇐$] : Rel[⇐$] (po src) (po dst)
  po[⇐$] = [⇐]→₂[⇐$] po[⇐]

  po[$⇒] : Rel[$⇒] (po src) (po dst)
  po[$⇒] = rel[$⇒] (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

  po[⇒] : Rel[⇒] (po src) (po dst)
  po[⇒] = [$⇒]→₂[⇒] po[$⇒]
  
  ¬po[⇒] : Rel[⇒] (¬₂ po src) (¬₂ po dst)
  ¬po[⇒] = ¬₂[⇒] po[⇐$]

  po-loc[⇒] : CRel[⇒] (po src ∩₂ SameLoc) (po dst ∩₂ SameLoc)
  po-loc[⇒] ¬x-elim ¬y-elim x∈src y∈src (po[xy] , xy-sloc) =
    po[⇒] x∈src y∈src po[xy] , sloc[⇒] ¬x-elim ¬y-elim x∈src y∈src xy-sloc

  udr-po[⇐] : Pred[⇐] (udr (po src)) (udr (po dst))
  udr-po[⇐] = udr[⇐] (po src) (po dst) (po∈ex dst-wf) po[⇐]

  udr-po[⇐$] : Pred[⇐$] (udr (po src)) (udr (po dst))
  udr-po[⇐$] = [⇐]→₁[⇐$] udr-po[⇐]


  -- ### Mapping - Relations: po⁺

  po⁺[⇒] : Rel[⇒] (TransClosure (po src)) (TransClosure (po dst))
  po⁺[⇒] = ⁺[⇒]ˡ poˡ∈src po[⇒]

  po⁺[⇐] : Rel[⇐] (TransClosure (po src)) (TransClosure (po dst))
  po⁺[⇐] = ⁺[⇐]ˡ (poˡ∈ex dst-wf) po[⇐]


  -- ### Mapping - Relations: pi

  pi[$⇒] : Rel[$⇒] (po-imm src) (po-imm dst)
  pi[$⇒] = imm[$⇒]ˡ (poˡ∈ex dst-wf) po[⇐] po[$⇒]

  pi[⇒] : Rel[⇒] (po-imm src) (po-imm dst)
  pi[⇒] = [$⇒]→₂[⇒] pi[$⇒]

  pi[⇐$] : Rel[⇐$] (po-imm src) (po-imm dst)
  pi[⇐$] = imm[⇐$]ˡ poˡ∈src po[⇒] po[⇐$]

  pi[⇐] : Rel[⇐] (po-imm src) (po-imm dst)
  pi[⇐] = [⇐$]→₂[⇐] pi[⇐$]


  -- ### Mapping - Relations: pi⁺

  pi⁺[⇒] : Rel[⇒] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
  pi⁺[⇒] = ⁺[⇒]ˡ (poˡ∈src ∘ proj₁) pi[⇒]

  pi⁺[$⇒] : Rel[$⇒] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
  pi⁺[$⇒] = [⇒]→₂[$⇒] pi⁺[⇒]

  pi⁺[⇐] : Rel[⇐] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
  pi⁺[⇐] = ⁺[⇐]ˡ (piˡ∈ex dst-wf) pi[⇐]

  pi⁺[⇐$] : Rel[⇐$] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
  pi⁺[⇐$] = [⇐]→₂[⇐$] pi⁺[⇐]


  co[⇒] : CRel[⇒] (co src) (co dst)
  co[⇒] = [$⇒]→₂[⇒]ᶜ co[$⇒]

  co[⇐$] : Rel[⇐$] (co src) (co dst)
  co[⇐$] = [⇐]→₂[⇐$] co[⇐]

  coe[⇒] : CRel[⇒] (coe src) (coe dst)
  coe[⇒] ¬x-elim ¬y-elim x∈src y∈src (co[xy] , ¬po[xy]) =
    co[⇒] ¬x-elim ¬y-elim x∈src y∈src co[xy] , ¬po[⇒] x∈src y∈src ¬po[xy]


  rf[⇒] : CRel[⇒] (rf src) (rf dst)
  rf[⇒] = [$⇒]→₂[⇒]ᶜ rf[$⇒]

  rf[⇐$] : Rel[⇐$] (rf src) (rf dst)
  rf[⇐$] = [⇐]→₂[⇐$] rf[⇐]

  rfe[⇒] : CRel[⇒] (rfe src) (rfe dst)
  rfe[⇒] ¬x-elim ¬y-elim x∈src y∈src (co[xy] , ¬po[xy]) =
    rf[⇒] ¬x-elim ¬y-elim x∈src y∈src co[xy] , ¬po[⇒] x∈src y∈src ¬po[xy]

  -- `fr[⇒]` cannot be proven generally, as it may go:
  -- `rf⁻¹ x src-elim-ev ⨾ co src-elim-ev y`
  -- in which it cannot go through the eliminated event in the target


  ord[⇒] : CRel[⇒] (OrdAlt src) (OrdAlt dst)
  ord[⇒] ¬x-elim ¬y-elim x∈src y∈src (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    ord-init ((refl , Init[⇒] x∈src x-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , RW[⇒] ¬y-elim y∈src y-rw))
  -- # R
  ord[⇒] ¬x-elim ¬y-elim x∈src y∈src (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-m))) =
    let z∈src = poʳ∈src po[xz]
    in ord-rm ((refl , R[⇒] ¬x-elim x∈src x-r) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , F₌[⇒] z∈src z-f) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy] ⨾[ _ ]⨾ (refl , RW[⇒] ¬y-elim y∈src y-m))
  -- # W
  ord[⇒] ¬x-elim ¬y-elim x∈src y∈src (ord-ww ((refl , x-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-w))) =
    let z∈src = poʳ∈src po[xz]
    in ord-ww ((refl , W[⇒] ¬x-elim x∈src x-w) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , F₌[⇒] z∈src z-f) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy] ⨾[ _ ]⨾ (refl , W[⇒] ¬y-elim y∈src y-w))
  -- # SC
  ord[⇒] ¬x-elim ¬y-elim x∈src y∈src (ord-sc ((refl , x-m) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-m))) =
    let z∈src = poʳ∈src po[xz]
    in ord-sc ((refl , RW[⇒] ¬x-elim x∈src x-m) ⨾[ _ ]⨾ po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , F₌[⇒] z∈src z-f) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy] ⨾[ _ ]⨾ (refl , RW[⇒] ¬y-elim y∈src y-m))
  ord[⇒] ¬x-elim ¬y-elim x∈src y∈src (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ))) =
    ord-rmw-dom ((refl , RW[⇒] ¬x-elim x∈src x-rw) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , rmwˡ[⇒] y∈src y∈rmwˡ))
  ord[⇒] ¬x-elim ¬y-elim x∈src y∈src (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    ord-rmw-codom ((refl , rmwʳ[⇒] x∈src x∈rmwʳ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , RW[⇒] ¬y-elim y∈src y-rw))
  ord[⇒] ¬x-elim ¬y-elim x∈src y∈src (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-wₐ))) =
    ord-w ((refl , RW[⇒] ¬x-elim x∈src x-rw) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , Wₐ[⇒] y∈src y-wₐ))
  ord[⇒] ¬x-elim ¬y-elim x∈src y∈src (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    ord-r ((refl , Rₐ[⇒] x∈src x-rₐ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , RW[⇒] ¬y-elim y∈src y-rw))


  -- # Utils
  
  elim-¬init : ¬ EvInit src-elim-ev
  elim-¬init elim-init = disjoint-init/rwₙₜ _ (elim-init , elim-r/w)
  
  elim-¬rₐ : ¬ EvRₜ trmw src-elim-ev
  elim-¬rₐ elim-r-rmw = disjoint-rwₜ _ (rwₙₜ⇒rwₜ elim-r/w , rₜ⇒rwₜ elim-r-rmw)
  
  elim-¬wₐ : ¬ EvWₜ trmw src-elim-ev
  elim-¬wₐ elim-w-rmw = disjoint-rwₜ _ (rwₙₜ⇒rwₜ elim-r/w , wₜ⇒rwₜ elim-w-rmw)


-- | Many wellformness components that are derived from the
-- `EliminationFramework`.
--
-- Note that /not all/ components can be derived from this framework. Individual
-- elimination proofs have to provide those for their specific scenario.
module WellFormed (δ : EliminationFramework) where

  open EliminationFramework δ
  open Ψ.GeneralFramework ψ
  open Ψ.Definitions ev[⇐]
  open Ψ.WellFormed ψ
  open Definitions δ

  
  -- # Wellformed
  
  src-rmw-def : src-rmw ⊆₂ immediate (po src)
  src-rmw-def = ⊆: lemma
    where
    lemma : src-rmw ⊆₂' immediate (po src)
    lemma x y rmw[xy] = 
      let x∈src = rmwˡ∈src rmw[xy]
          y∈src = rmwʳ∈src rmw[xy]
          dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
          dst-pi[xy] = ⊆₂-apply (rmw-def dst-wf) dst-rmw[xy]
      in pi[⇐$] x∈src y∈src dst-pi[xy]


  src-rmw-w : codom (src-rmw) ⇔₁ (src-events ∩₁ EvWₜ trmw)
  src-rmw-w = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : codom (src-rmw) ⊆₁' (src-events ∩₁ EvWₜ trmw)
    ⊆-proof y (x , rmw[xy]) =
      let x∈src = rmwˡ∈src rmw[xy]
          y∈src = rmwʳ∈src rmw[xy]
          dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
          (_ , dst-y-w) = ⇔₁-apply-⊆₁ (rmw-w dst-wf) (ev[⇒] x∈src , dst-rmw[xy])
      in y∈src , Wₜ[⇐$] y∈src dst-y-w

    ⊇-proof : (src-events ∩₁ EvWₜ trmw) ⊆₁' codom (src-rmw)
    ⊇-proof y (y∈src , y-w) =
      let ¬y-elim = λ{refl → disjoint-rwₜ _ (rwₙₜ⇒rwₜ elim-r/w , wₜ⇒rwₜ y-w)}
          (x , dst-rmw[xy]) = ⇔₁-apply-⊇₁ (rmw-w dst-wf) (events[⇒] y∈src , Wₜ[⇒] ¬y-elim y∈src y-w)
          x∈dst = rmwˡ∈ex dst-wf dst-rmw[xy]
      in ev[⇐] x∈dst , rmw[⇐$] (events[⇐] x∈dst) y∈src dst-rmw[xy]


  src-rmw-r×w : src-rmw ⊆₂ EvRₜ trmw ×₂ EvWₜ trmw
  src-rmw-r×w = ⊆: lemma
    where
    lemma : src-rmw ⊆₂' EvRₜ trmw ×₂ EvWₜ trmw
    lemma _ _ rmw[xy] = 
      let x∈src = rmwˡ∈src rmw[xy]
          y∈src = rmwʳ∈src rmw[xy]
          dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
          (x-r , y-w) = ⊆₂-apply (rmw-r×w dst-wf) dst-rmw[xy]
      in Rₜ[⇐$] x∈src x-r , Wₜ[⇐$] y∈src y-w


  src-po-init-first : ⊤-Precedes-⊥ EvInit (po src)
  src-po-init-first po[xy] y-init =
    let x∈src = poˡ∈src po[xy]
        y∈src = poʳ∈src po[xy]
        dst-po[xy] = po[⇒] x∈src y∈src po[xy]
        dst-y-init = Init[⇒] y∈src y-init
        dst-x-init = po-init-first dst-wf dst-po[xy] dst-y-init
    in Init[⇐$] x∈src dst-x-init


  src-po-tri : (tid : ThreadId) → Trichotomous _≡_ (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ src-events) (po src))
  src-po-tri tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src))
    with po-tri dst-wf tid (with-pred (ev[⇒] x∈src) (init/tid[⇒] x∈src x-init/tid , events[⇒] x∈src)) (with-pred (ev[⇒] y∈src) (init/tid[⇒] y∈src y-init/tid , events[⇒] y∈src))
  ... | tri<  po[xy] x≢y ¬po[yx] = tri< (po[⇐$] x∈src y∈src po[xy])   (λ{refl → x≢y refl}) (¬po[yx] ∘ po[⇒] y∈src x∈src)
  ... | tri≈ ¬po[xy] x≡y ¬po[yx] = tri≈ (¬po[xy] ∘ po[⇒] x∈src y∈src) lemma (¬po[yx] ∘ po[⇒] y∈src x∈src)
    where
    unique-pred : UniquePred ((EvInit ∪₁ HasTid tid) ∩₁ src-events)
    unique-pred =
      ∩₁-unique-pred (∪₁-unique-pred (λ{_ (ev-init , ())}) init-unique has-tid-unique) src-events-unique
    lemma : with-pred x (x-init/tid , x∈src) ≡ with-pred y (y-init/tid , y∈src)
    lemma = with-pred-unique unique-pred (ev[⇐$]eq x∈src y∈src (with-pred-≡ x≡y)) (x-init/tid , x∈src) (y-init/tid , y∈src)
  ... | tri> ¬po[xy] x≢y  po[yx] = tri> (¬po[xy] ∘ po[⇒] x∈src y∈src) (λ{refl → x≢y refl}) (po[⇐$] y∈src x∈src po[yx])


  src-po-splittable : SplittableOrder (po src)
  src-po-splittable = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : po src ⊆₂' TransClosure (po-imm src)
    ⊆-proof _ _ po[xy] =
      let x∈src = poˡ∈src po[xy]
          y∈src = poʳ∈src po[xy]
          dst-po[xy] = po[⇒] x∈src y∈src po[xy]
          dst-pi⁺[xy] = ⇔₂-apply-⊆₂ (po-splittable dst-wf) dst-po[xy]
      in pi⁺[⇐$] x∈src y∈src dst-pi⁺[xy]

    ⊇-proof : TransClosure (po-imm src) ⊆₂' po src
    ⊇-proof _ _ pi⁺[xy] = 
      let x∈src = ⁺-lift-predˡ (poˡ∈src ∘ proj₁) pi⁺[xy]
          y∈src = ⁺-lift-predʳ (poʳ∈src ∘ proj₁) pi⁺[xy]
          dst-pi⁺[xy] = pi⁺[⇒] x∈src y∈src pi⁺[xy]
          dst-po[xy] = ⇔₂-apply-⊇₂ (po-splittable dst-wf) dst-pi⁺[xy]
      in po[⇐$] x∈src y∈src dst-po[xy]


  src-po-elements : udr (po src) ⇔₁ events src
  src-po-elements = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : udr (po src) ⊆₁' events src
    ⊆-proof _ = udr-po∈src

    ⊇-proof : src-events ⊆₁' udr (po src)
    ⊇-proof x x∈src = udr-po[⇐$] x∈src (⇔₁-apply-⊇₁ (po-elements dst-wf) (events[⇒] x∈src))


  src-po-stid : po src ⊆₂ ( EvInit ×₂ EvE ) ∪₂ SameTid
  src-po-stid = ⊆: lemma
    where
    lemma : po src ⊆₂' ( EvInit ×₂ EvE ) ∪₂ SameTid
    lemma x y po[xy] =
      let x∈src = poˡ∈src po[xy]
          y∈src = poʳ∈src po[xy]
          dst-po[xy] = po[⇒] x∈src y∈src po[xy]
          xy-init+e/stid = ⊆₂-apply (po-stid dst-wf) dst-po[xy]
      in init+e/stid[⇐$] x∈src y∈src xy-init+e/stid


  src-rmw-sloc : rmw src ⊆₂ SameLoc
  src-rmw-sloc = ⊆: lemma
    where
    lemma : rmw src ⊆₂' SameLoc
    lemma x y rmw[xy] =
      let x∈src = rmwˡ∈src rmw[xy]
          y∈src = rmwʳ∈src rmw[xy]
          dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
          xy-sloc = ⊆₂-apply (rmw-sloc dst-wf) dst-rmw[xy]
      in sloc[⇐$] x∈src y∈src xy-sloc      


  src-wf-init-≥1 : (loc : Location) → NonEmpty₁ (EvInit ∩₁ HasLoc loc ∩₁ src-events)
  src-wf-init-≥1 loc =
    let (x , x-init , x-loc , x∈dst) = wf-init-≥1 dst-wf loc
        x∈src = events[⇐] x∈dst
    in ev[⇐] x∈dst , Init[⇐$] x∈src x-init , loc[⇐$] x∈src x-loc , x∈src

  src-wf-init-≤1 : (loc : Location) → Unique₁ _≡_ (EvInit ∩₁ HasLoc loc ∩₁ src-events)
  src-wf-init-≤1 loc {x} {y} (x-init , x-loc , x∈src) (y-init , y-loc , y∈src) =
    let ¬x-elim = λ{refl → elim-¬init x-init}
        ¬y-elim = λ{refl → elim-¬init y-init}
        dst-x≡y = wf-init-≤1 dst-wf loc
                    (Init[⇒] x∈src x-init , loc[⇒] ¬x-elim x∈src x-loc , events[⇒] x∈src)
                    (Init[⇒] y∈src y-init , loc[⇒] ¬y-elim y∈src y-loc , events[⇒] y∈src)
    in ev[⇐$]eq x∈src y∈src dst-x≡y
