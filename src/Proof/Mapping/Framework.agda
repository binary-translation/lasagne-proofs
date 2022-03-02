{-# OPTIONS --safe #-}

open import Arch.General.Event using (LabelClass)
import Arch.General.Execution as Ex


-- | A framework for mapping proofs between two architectures.
--
-- This framework extends the general framework (specified in `Proof.Framework`), with
-- additional property mappings (e.g., mapping of `Location`).
--
-- Note that this mapping framework stands in contrast to the elimination framework
-- (in `Proof.Elimination.Framework`), which does /not/ generally map these same
-- properties.
module Proof.Mapping.Framework
  (LabelSrc : Set) {{_ : LabelClass LabelSrc}}
  {LabelDst : Set} {{_ : LabelClass LabelDst}}
  (dst : Ex.Execution LabelDst)
  (dst-wf : Ex.WellFormed dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst) renaming (sym to ≡-sym)
open import Function using (_∘_; flip)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary using (Transitive; Trichotomous; IsStrictTotalOrder; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution hiding (WellFormed; Execution)
open import Arch.General.Properties
open import Arch.General.DerivedWellformed
-- Local imports: Proof Components
import Proof.Framework LabelSrc dst dst-wf as Ψ


open Ex.Execution
open Ex.WellFormed


-- | A framework for mapping proofs between two architectures.
record MappingFramework : Set₁ where
  field
    -- # Definitions
    ψ : Ψ.GeneralFramework

  -- This seems to work. Interesting..
  open Ψ.Definitions (Ψ.GeneralFramework.ev[⇐] ψ) using (Pred[⇐]²; Pred[$⇒]²)
  
  field
    -- # Properties
    
    loc[⇐]   : {loc : Location} → Pred[⇐]²  (HasLoc loc)
    loc[$⇒]  : {loc : Location} → Pred[$⇒]² (HasLoc loc)
    val[⇐]   : {val : Value}    → Pred[⇐]²  (HasVal val)
    val[$⇒]  : {val : Value}    → Pred[$⇒]² (HasVal val)
    Wₜ[⇐]    : {tag : Tag}      → Pred[⇐]²  (EvWₜ tag)
    Wₜ[$⇒]   : {tag : Tag}      → Pred[$⇒]² (EvWₜ tag)
    Rₜ[⇐]    : {tag : Tag}      → Pred[⇐]²  (EvRₜ tag)
    Rₜ[$⇒]   : {tag : Tag}      → Pred[$⇒]² (EvRₜ tag)


module Definitions (δ : MappingFramework) where

  open MappingFramework δ
  open Ψ.GeneralFramework ψ
  open Ψ.Definitions ev[⇐]
  open Ψ.WellFormed ψ


  -- # Execution

  src : Ex.Execution LabelSrc
  src =
    record {
      events = src-events
    ; po     = src-rel (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)
    ; rf     = src-rel (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)
    ; co     = src-rel (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)
    ; rmw    = src-rmw
    }


  -- # Mapping

  -- # Helpers: Types


  poˡ∈src : po src ˡ∈src
  poˡ∈src = relˡ∈src (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

  poʳ∈src : po src ʳ∈src
  poʳ∈src = relʳ∈src (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

  udr-po∈src : udr[ po src ]∈src
  udr-po∈src = lr→udr (po src) poˡ∈src poʳ∈src


  rfˡ∈src : rf src ˡ∈src
  rfˡ∈src = relˡ∈src (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

  rfʳ∈src : rf src ʳ∈src
  rfʳ∈src = relʳ∈src (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

  udr-rf∈src : udr[ rf src ]∈src
  udr-rf∈src = lr→udr (rf src) rfˡ∈src rfʳ∈src


  coˡ∈src : co src ˡ∈src
  coˡ∈src = relˡ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

  coʳ∈src : co src ʳ∈src
  coʳ∈src = relʳ∈src (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

  udr-co∈src : udr[ co src ]∈src
  udr-co∈src = lr→udr (co src) coˡ∈src coʳ∈src


  frˡ∈src : fr src ˡ∈src
  frˡ∈src (rf⁻¹[xz] ⨾[ z ]⨾ co[zy]) = rfʳ∈src rf⁻¹[xz]
  
  frʳ∈src : fr src ʳ∈src
  frʳ∈src (rf⁻¹[xz] ⨾[ z ]⨾ co[zy]) = coʳ∈src co[zy]
  
  udr-fr∈src : udr[ fr src ]∈src
  udr-fr∈src = lr→udr (fr src) frˡ∈src frʳ∈src
  

  -- # Mapping

  -- ## Mapping: Predicates

  loc[⇒] : ∀ {loc : Location} → Pred[⇒]² (HasLoc loc)
  loc[⇒]  = [$⇒]→₁[⇒] loc[$⇒]

  loc[⇐$] : ∀ {loc : Location} → Pred[⇐$]² (HasLoc loc)
  loc[⇐$] = [⇐]→₁[⇐$] loc[⇐]


  val[⇒] : ∀ {val : Value} → Pred[⇒]² (HasVal val)
  val[⇒]  = [$⇒]→₁[⇒] val[$⇒]

  val[⇐$] : ∀ {val : Value} → Pred[⇐$]² (HasVal val)
  val[⇐$] = [⇐]→₁[⇐$] val[⇐]


  -- ## Mapping: Derived Predicates

  sloc[⇒] : Rel[⇒]² SameLoc
  sloc[⇒] x∈src y∈src (same-loc x-loc y-loc) =
    same-loc (loc[⇒] x∈src x-loc) (loc[⇒] y∈src y-loc)

  sloc[⇐$] : Rel[⇐$]² SameLoc
  sloc[⇐$] x∈src y∈src (same-loc x-loc y-loc) =
    same-loc (loc[⇐$] x∈src x-loc) (loc[⇐$] y∈src y-loc)

  sval[⇒] : Rel[⇒]² SameVal
  sval[⇒] x∈src y∈src (same-val x-val y-val) =
    same-val (val[⇒] x∈src x-val) (val[⇒] y∈src y-val)

  sval[⇐$] : Rel[⇐$]² SameVal
  sval[⇐$] x∈src y∈src (same-val x-val y-val) =
    same-val (val[⇐$] x∈src x-val) (val[⇐$] y∈src y-val)


  Wₜ[⇒] : {tag : Tag} → Pred[⇒]² (EvWₜ tag)
  Wₜ[⇒] {tag} x∈src = Wₜ[$⇒] (events[⇒] x∈src) ∘ (subst (EvWₜ tag) (ev[⇒⇐] x∈src))

  Wₜ[⇐$] : {tag : Tag} → Pred[⇐$]² (EvWₜ tag)
  Wₜ[⇐$] {tag} x∈src = subst (EvWₜ tag) (≡-sym (ev[⇒⇐] x∈src)) ∘ Wₜ[⇐] (events[⇒] x∈src)


  W[⇐$] : Pred[⇐$]² EvW
  W[⇐$] x∈src = wₜ⇒w ∘ Wₜ[⇐$] x∈src ∘ w⇒wₜ

  W[⇒] : Pred[⇒]² EvW
  W[⇒] x∈src = wₜ⇒w ∘ Wₜ[⇒] x∈src ∘ w⇒wₜ
  
  W[⇐] : Pred[⇐]² EvW
  W[⇐] x∈dst = wₜ⇒w ∘ Wₜ[⇐] x∈dst ∘ w⇒wₜ
  
  
  Rₜ[⇐$] : {tag : Tag} → Pred[⇐$]² (EvRₜ tag)
  Rₜ[⇐$] {tag} x∈src = subst (EvRₜ tag) (≡-sym (ev[⇒⇐] x∈src)) ∘ Rₜ[⇐] (events[⇒] x∈src)
  
  Rₜ[⇒] : {tag : Tag} → Pred[⇒]² (EvRₜ tag)
  Rₜ[⇒] {tag} x∈src = Rₜ[$⇒] (events[⇒] x∈src) ∘ (subst (EvRₜ tag) (ev[⇒⇐] x∈src))

  R[⇐$] : Pred[⇐$]² EvR
  R[⇐$] x∈src = rₜ⇒r ∘ Rₜ[⇐$] x∈src ∘ r⇒rₜ
  
  R[⇒] : Pred[⇒]² EvR
  R[⇒] x∈src = rₜ⇒r ∘ Rₜ[⇒] x∈src ∘ r⇒rₜ


  RW[⇒] : Pred[⇒]² EvRW
  RW[⇒] x∈src x-rw with rw/rw x-rw
  RW[⇒] x∈src x-rw | inj₁ x-r = r⇒rw (R[⇒] x∈src x-r)
  RW[⇒] x∈src x-rw | inj₂ x-w = w⇒rw (W[⇒] x∈src x-w)
  

  -- ## Mapping: Relations

  po[⇐] : Rel[⇐] (po src) (po dst)
  po[⇐] = rel[⇐] (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

  po[$⇒] : Rel[$⇒] (po src) (po dst)
  po[$⇒] = rel[$⇒] (poˡ∈ex dst-wf) (poʳ∈ex dst-wf)

  po[⇐$] : Rel[⇐$] (po src) (po dst)
  po[⇐$] = [⇐]→₂[⇐$] po[⇐]

  po[⇒] : Rel[⇒] (po src) (po dst)
  po[⇒] = [$⇒]→₂[⇒] po[$⇒]


  ¬po[⇒] : Rel[⇒] (¬₂ po src) (¬₂ po dst)
  ¬po[⇒] = ¬₂[⇒] po[⇐$]

  po-loc[⇒] : Rel[⇒] (po-loc src) (po-loc dst)
  po-loc[⇒] = ∩₂[⇒] po[⇒] sloc[⇒]

  po⁺[⇒] : Rel[⇒] (TransClosure (po src)) (TransClosure (po dst))
  po⁺[⇒] = ⁺[⇒]ˡ poˡ∈src po[⇒]

  udr-po[⇐] : Pred[⇐] (udr (po src)) (udr (po dst))
  udr-po[⇐] = udr[⇐] (po src) (po dst) (po∈ex dst-wf) po[⇐]
  
  udr-po[⇐$] : Pred[⇐$] (udr (po src)) (udr (po dst))
  udr-po[⇐$] = [⇐]→₁[⇐$] udr-po[⇐]


  po⁺[⇐] : Rel[⇐] (TransClosure (po src)) (TransClosure (po dst))
  po⁺[⇐] = ⁺[⇐]ˡ (poˡ∈ex dst-wf) po[⇐]

  pi[$⇒] : Rel[$⇒] (po-imm src) (po-imm dst)
  pi[$⇒] = imm[$⇒]ˡ (poˡ∈ex dst-wf) po[⇐] po[$⇒]

  pi[⇒] : Rel[⇒] (po-imm src) (po-imm dst)
  pi[⇒] = [$⇒]→₂[⇒] pi[$⇒]

  pi[⇐$] : Rel[⇐$] (po-imm src) (po-imm dst)
  pi[⇐$] = imm[⇐$]ˡ poˡ∈src po[⇒] po[⇐$]

  pi[⇐] : Rel[⇐] (po-imm src) (po-imm dst)
  pi[⇐] = [⇐$]→₂[⇐] pi[⇐$]

  pi⁺[⇒] : Rel[⇒] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
  pi⁺[⇒] = ⁺[⇒]ˡ (poˡ∈src ∘ proj₁) pi[⇒]

  pi⁺[$⇒] : Rel[$⇒] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
  pi⁺[$⇒] = [⇒]→₂[$⇒] pi⁺[⇒]
  
  pi⁺[⇐] : Rel[⇐] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
  pi⁺[⇐] = ⁺[⇐]ˡ (poˡ∈ex dst-wf ∘ proj₁) pi[⇐]
  
  pi⁺[⇐$] : Rel[⇐$] (TransClosure (po-imm src)) (TransClosure (po-imm dst))
  pi⁺[⇐$] = [⇐]→₂[⇐$] pi⁺[⇐]


  rf[$⇒] : Rel[$⇒] (rf src) (rf dst)
  rf[$⇒] = rel[$⇒] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)
    
  rf[⇒] : Rel[⇒] (rf src) (rf dst)
  rf[⇒] = [$⇒]→₂[⇒] rf[$⇒]
  
  rf[⇐] : Rel[⇐] (rf src) (rf dst)
  rf[⇐] = rel[⇐] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)

  rf[⇐$] : Rel[⇐$] (rf src) (rf dst)
  rf[⇐$] = [⇐]→₂[⇐$] rf[⇐]
  
  rfe[⇒] : Rel[⇒] (rfe src) (rfe dst)
  rfe[⇒] = ∩₂[⇒] rf[⇒] ¬po[⇒]


  co[$⇒] : Rel[$⇒] (co src) (co dst)
  co[$⇒] = rel[$⇒] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

  co[⇒] : Rel[⇒] (co src) (co dst)
  co[⇒] = [$⇒]→₂[⇒] co[$⇒]

  co[⇐] : Rel[⇐] (co src) (co dst)
  co[⇐] = rel[⇐] (coˡ∈ex dst-wf) (coʳ∈ex dst-wf)

  co[⇐$] : Rel[⇐$] (co src) (co dst)
  co[⇐$] = [⇐]→₂[⇐$] co[⇐]

  coe[⇒] : Rel[⇒] (coe src) (coe dst)
  coe[⇒] = ∩₂[⇒] co[⇒] ¬po[⇒]
  

  fr[⇒] : Rel[⇒] (fr src) (fr dst)
  fr[⇒] x∈src y∈src (rf⁻¹[xz] ⨾[ z ]⨾ co[zy]) =
    let z∈src = coˡ∈src co[zy]
    in rf[⇒] z∈src x∈src rf⁻¹[xz] ⨾[ ev[⇒] z∈src ]⨾ co[⇒] z∈src y∈src co[zy]
  
  fre[⇒] : Rel[⇒] (fre src) (fre dst)
  fre[⇒] = ∩₂[⇒] fr[⇒] ¬po[⇒]


-- | All requirements of wellformedness can be derived with an instance of
-- `MappingFramework`, which is given here.
module WellFormed (δ : MappingFramework) where

  open MappingFramework δ
  open Ψ.GeneralFramework ψ
  open Ψ.Definitions ev[⇐]
  open Ψ.WellFormed ψ
  open Definitions δ
  
  
  -- # Wellformed

  src-rmw-def : rmw src ⊆₂ po-imm src
  src-rmw-def = ⊆: lemma
    where
    lemma : rmw src ⊆₂' po-imm src
    lemma x y rmw[xy] = 
      let x∈src = rmwˡ∈src rmw[xy]
          y∈src = rmwʳ∈src rmw[xy]
          dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
          dst-pi[xy] = ⊆₂-apply (rmw-def dst-wf) dst-rmw[xy]
      in pi[⇐$] x∈src y∈src dst-pi[xy]


  src-rmw-w : codom (rmw src) ⇔₁ (events src ∩₁ EvWₜ trmw)
  src-rmw-w = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : codom (rmw src) ⊆₁' (events src ∩₁ EvWₜ trmw)
    ⊆-proof y (x , rmw[xy]) =
      let x∈src = rmwˡ∈src rmw[xy]
          y∈src = rmwʳ∈src rmw[xy]
          dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
          (_ , dst-y-w) = ⇔₁-apply-⊆₁ (rmw-w dst-wf) (ev[⇒] x∈src , dst-rmw[xy])
      in y∈src , Wₜ[⇐$] y∈src dst-y-w

    ⊇-proof : (events src ∩₁ EvWₜ trmw) ⊆₁' codom (rmw src)
    ⊇-proof y (y∈src , y-w) =
      let (x , dst-rmw[xy]) = ⇔₁-apply-⊇₁ (rmw-w dst-wf) (events[⇒] y∈src , Wₜ[⇒] y∈src y-w)
          x∈dst = rmwˡ∈ex dst-wf dst-rmw[xy]
      in (ev[⇐] x∈dst , rmw[⇐$] (events[⇐] x∈dst) y∈src dst-rmw[xy])


  src-rf-w×r : rf src ⊆₂ EvW ×₂ EvR
  src-rf-w×r = ⊆: lemma
    where
    lemma : rf src ⊆₂' EvW ×₂ EvR
    lemma x y rf[xy] =
      let x∈src = rfˡ∈src rf[xy]
          y∈src = rfʳ∈src rf[xy]
          dst-rf[xy] = rf[⇒] x∈src y∈src rf[xy]
          (x-w , y-r) = ⊆₂-apply (rf-w×r dst-wf) dst-rf[xy]
      in W[⇐$] x∈src x-w , R[⇐$] y∈src y-r


  src-co-w×w : co src ⊆₂ EvW ×₂ EvW
  src-co-w×w = ⊆: lemma
    where
    lemma : co src ⊆₂' EvW ×₂ EvW
    lemma x y co[xy] =
      let x∈src = coˡ∈src co[xy]
          y∈src = coʳ∈src co[xy]
          dst-co[xy] = co[⇒] x∈src y∈src co[xy]
          (x-w , y-w) = ⊆₂-apply (co-w×w dst-wf) dst-co[xy]
      in W[⇐$] x∈src x-w , W[⇐$] y∈src y-w


  src-rmw-r×w : rmw src ⊆₂ EvRₜ trmw ×₂ EvWₜ trmw
  src-rmw-r×w = ⊆: lemma
    where
    lemma : rmw src ⊆₂' EvRₜ trmw ×₂ EvWₜ trmw
    lemma x y rmw[xy] = 
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


  src-co-init-first : ⊤-Precedes-⊥ EvInit (co src)
  src-co-init-first co[xy] y-init =
    let x∈src = coˡ∈src co[xy]
        y∈src = coʳ∈src co[xy]
        dst-co[xy] = co[⇒] x∈src y∈src co[xy]
        dst-y-init = Init[⇒] y∈src y-init
        dst-x-init = co-init-first dst-wf dst-co[xy] dst-y-init
    in Init[⇐$] x∈src dst-x-init


  src-po-tri : (tid : ThreadId) → Trichotomous _≡_ (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ events src) (po src))
  src-po-tri tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src))
    with po-tri dst-wf tid (with-pred (ev[⇒] x∈src) (init/tid[⇒] x∈src x-init/tid , events[⇒] x∈src)) (with-pred (ev[⇒] y∈src) (init/tid[⇒] y∈src y-init/tid , events[⇒] y∈src))
  ... | tri<  po[xy] x≢y ¬po[yx] = tri< (po[⇐$] x∈src y∈src po[xy])   (λ{refl → x≢y refl}) (¬po[yx] ∘ po[⇒] y∈src x∈src)
  ... | tri≈ ¬po[xy] x≡y ¬po[yx] = tri≈ (¬po[xy] ∘ po[⇒] x∈src y∈src) lemma (¬po[yx] ∘ po[⇒] y∈src x∈src)
    where
    unique-pred : UniquePred ((EvInit ∪₁ HasTid tid) ∩₁ events src)
    unique-pred =
      ∩₁-unique-pred (∪₁-unique-pred (λ{_ (ev-init , ())}) init-unique has-tid-unique) src-events-unique
    lemma : with-pred x (x-init/tid , x∈src) ≡ with-pred y (y-init/tid , y∈src)
    lemma = with-pred-unique unique-pred (ev[⇐$]eq x∈src y∈src (with-pred-≡ x≡y)) (x-init/tid , x∈src) (y-init/tid , y∈src)
  ... | tri> ¬po[xy] x≢y  po[yx] = tri> (¬po[xy] ∘ po[⇒] x∈src y∈src) (λ{refl → x≢y refl}) (po[⇐$] y∈src x∈src po[yx])


  src-co-tri : (loc : Location) → Trichotomous _≡_ (filter-rel (EvW ∩₁ HasLoc loc ∩₁ events src) (co src))
  src-co-tri loc (with-pred x (x-w , x-loc , x∈src)) (with-pred y (y-w , y-loc , y∈src))
    with co-tri dst-wf loc (with-pred (ev[⇒] x∈src) (W[⇒] x∈src x-w , loc[⇒] x∈src x-loc , events[⇒] x∈src)) (with-pred (ev[⇒] y∈src) (W[⇒] y∈src y-w , loc[⇒] y∈src y-loc , events[⇒] y∈src))
  ... | tri<  co[xy] x≢y ¬co[yx] = tri< (co[⇐$] x∈src y∈src co[xy]) (λ{refl → x≢y refl}) (¬co[yx] ∘ co[⇒] y∈src x∈src)
  ... | tri≈ ¬co[xy] x≡y ¬co[yx] = tri≈ (¬co[xy] ∘ co[⇒] x∈src y∈src) lemma (¬co[yx] ∘ co[⇒] y∈src x∈src)
    where
    unique-pred : UniquePred (EvW ∩₁ HasLoc loc ∩₁ events src)
    unique-pred = ∩₁-unique-pred w-unique (∩₁-unique-pred has-loc-unique src-events-unique)
    lemma : with-pred x (x-w , x-loc , x∈src) ≡ with-pred y (y-w , y-loc , y∈src)
    lemma = with-pred-unique unique-pred (ev[⇐$]eq x∈src y∈src (with-pred-≡ x≡y)) (x-w , x-loc , x∈src) (y-w , y-loc , y∈src)
  ... | tri> ¬co[xy] x≢y  co[yx] = tri> (¬co[xy] ∘ co[⇒] x∈src y∈src) (λ{refl → x≢y refl}) (co[⇐$] y∈src x∈src co[yx])


  src-po-splittable : SplittableOrder (po src)
  src-po-splittable = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : po src ⊆₂' TransClosure (po-imm src)
    ⊆-proof x y po[xy] =
      let x∈src = poˡ∈src po[xy]
          y∈src = poʳ∈src po[xy]
          dst-po[xy] = po[⇒] x∈src y∈src po[xy]
          dst-pi⁺[xy] = ⇔₂-apply-⊆₂ (po-splittable dst-wf) dst-po[xy]
      in pi⁺[⇐$] x∈src y∈src dst-pi⁺[xy]

    ⊇-proof : TransClosure (po-imm src) ⊆₂' po src
    ⊇-proof x y pi⁺[xy] = 
      let x∈src = ⁺-lift-predˡ (poˡ∈src ∘ proj₁) pi⁺[xy]
          y∈src = ⁺-lift-predʳ (poʳ∈src ∘ proj₁) pi⁺[xy]
          dst-pi⁺[xy] = pi⁺[⇒] x∈src y∈src pi⁺[xy]
          dst-po[xy] = ⇔₂-apply-⊇₂ (po-splittable dst-wf) dst-pi⁺[xy]
      in po[⇐$] x∈src y∈src dst-po[xy]


  src-co-trans : Transitive (co src)
  src-co-trans co[xy] co[yz] =
    let x∈src = coˡ∈src co[xy]
        y∈src = coʳ∈src co[xy]
        z∈src = coʳ∈src co[yz]
        dst-co[xy] = co[⇒] x∈src y∈src co[xy]
        dst-co[yz] = co[⇒] y∈src z∈src co[yz]
        dst-co[xz] = co-trans dst-wf dst-co[xy] dst-co[yz]
    in co[⇐$] x∈src z∈src dst-co[xz]


  src-po-elements : udr (po src) ⇔₁ events src
  src-po-elements = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : udr (po src) ⊆₁' events src
    ⊆-proof _ = udr-po∈src

    ⊇-proof : events src ⊆₁' udr (po src)
    ⊇-proof x x∈src = udr-po[⇐$] x∈src (⇔₁-apply-⊇₁ (po-elements dst-wf) (events[⇒] x∈src))


  src-rf-elements : udr (rf src) ⊆₁ events src
  src-rf-elements = ⊆: (λ _ → udr-rf∈src)


  src-co-elements : udr (co src) ⊆₁ events src
  src-co-elements = ⊆: (λ _ → udr-co∈src)


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


  src-rf-sloc : rf src ⊆₂ SameLoc
  src-rf-sloc = ⊆: lemma
    where
    lemma : rf src ⊆₂' SameLoc
    lemma x y rf[xy] =
      let x∈src = rfˡ∈src rf[xy]
          y∈src = rfʳ∈src rf[xy]
          dst-rf[xy] = rf[⇒] x∈src y∈src rf[xy]
          xy-sloc = ⊆₂-apply (rf-sloc dst-wf) dst-rf[xy]
      in sloc[⇐$] x∈src y∈src xy-sloc


  src-co-sloc : co src ⊆₂ SameLoc
  src-co-sloc = ⊆: lemma
    where
    lemma : co src ⊆₂' SameLoc
    lemma x y co[xy] =
      let x∈src = coˡ∈src co[xy]
          y∈src = coʳ∈src co[xy]
          dst-co[xy] = co[⇒] x∈src y∈src co[xy]
          xy-sloc = ⊆₂-apply (co-sloc dst-wf) dst-co[xy]
      in sloc[⇐$] x∈src y∈src xy-sloc


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


  src-rf-sval : rf src ⊆₂ SameVal
  src-rf-sval = ⊆: lemma
    where
    lemma : rf src ⊆₂' SameVal
    lemma x y rf[xy] =
      let x∈src = rfˡ∈src rf[xy]
          y∈src = rfʳ∈src rf[xy]
          dst-rf[xy] = rf[⇒] x∈src y∈src rf[xy]
          xy-sval = ⊆₂-apply (rf-sval dst-wf) dst-rf[xy]
      in sval[⇐$] x∈src y∈src xy-sval


  src-wf-rf-≥1 : (EvR ∩₁ events src) ⊆₁ codom (rf src)
  src-wf-rf-≥1 = ⊆: lemma
    where
    lemma : (EvR ∩₁ events src) ⊆₁' codom (rf src)
    lemma x (x-r , x∈src) =
      let x∈dst = events[⇒] x∈src
          (y , rf[yx]) = ⊆₁-apply (wf-rf-≥1 dst-wf) (R[⇒] x∈src x-r , x∈dst)
          y∈dst = rfˡ∈ex dst-wf rf[yx]
      in take-codom (rf src) (rf[⇐$] (events[⇐] y∈dst) x∈src rf[yx])


  src-wf-rf-≤1 : Functional _≡_ (flip (rf src))
  src-wf-rf-≤1 x y₁ y₂ rf[y₁x] rf[y₂x] =
    let x∈src = rfʳ∈src rf[y₁x]
        y₁∈src = rfˡ∈src rf[y₁x]
        y₂∈src = rfˡ∈src rf[y₂x]
        dst-rf[y₁x] = rf[⇒] y₁∈src x∈src rf[y₁x]
        dst-rf[y₂x] = rf[⇒] y₂∈src x∈src rf[y₂x]
        dst-y₁≡y₂ = wf-rf-≤1 dst-wf (ev[⇒] x∈src) (ev[⇒] y₁∈src) (ev[⇒] y₂∈src) dst-rf[y₁x] dst-rf[y₂x]
    in ev[⇐$]eq y₁∈src y₂∈src dst-y₁≡y₂


  src-wf-init-≥1 : (loc : Location) → NonEmpty₁ (EvInit ∩₁ HasLoc loc ∩₁ events src)
  src-wf-init-≥1 loc =
    let (x , x-init , x-loc , x∈dst) = wf-init-≥1 dst-wf loc
        x∈src = events[⇐] x∈dst
    in ev[⇐] x∈dst , Init[⇐$] x∈src x-init , loc[⇐$] x∈src x-loc , x∈src


  src-wf-init-≤1 : (loc : Location) → Unique₁ _≡_ (EvInit ∩₁ HasLoc loc ∩₁ events src)
  src-wf-init-≤1 loc (x-init , x-loc , x∈src) (y-init , y-loc , y∈src) =
    let dst-x≡y = wf-init-≤1 dst-wf loc
                    (Init[⇒] x∈src x-init , loc[⇒] x∈src x-loc , events[⇒] x∈src)
                    (Init[⇒] y∈src y-init , loc[⇒] y∈src y-loc , events[⇒] y∈src)
    in ev[⇐$]eq x∈src y∈src dst-x≡y


  src-wf : Ex.WellFormed src
  src-wf =
    record
      { unique-ids     = src-unique-ids
      ; events-unique  = src-events-unique
      ; rmw-def        = src-rmw-def
      ; rmw-w          = src-rmw-w
      ; rf-w×r         = src-rf-w×r
      ; co-w×w         = src-co-w×w
      ; rmw-r×w        = src-rmw-r×w
      ; po-init-first  = src-po-init-first
      ; co-init-first  = src-co-init-first
      ; po-tri         = src-po-tri
      ; co-tri         = src-co-tri
      ; po-splittable  = src-po-splittable
      ; co-trans       = src-co-trans
      ; events-uid-dec = src-events-uid-dec
      ; rmwˡ-dec       = src-rmwˡ-dec
      ; po-elements    = src-po-elements
      ; rf-elements    = src-rf-elements
      ; co-elements    = src-co-elements
      ; po-stid        = src-po-stid
      ; rf-sloc        = src-rf-sloc
      ; co-sloc        = src-co-sloc
      ; rmw-sloc       = src-rmw-sloc
      ; rf-sval        = src-rf-sval
      ; wf-rf-≥1       = src-wf-rf-≥1
      ; wf-rf-≤1       = src-wf-rf-≤1
      ; wf-init-≥1     = src-wf-init-≥1
      ; wf-init-≤1     = src-wf-init-≤1
      }


module Behavior (δ : MappingFramework) where

  open MappingFramework δ
  open Definitions δ
  open Ψ.GeneralFramework ψ
  open Ψ.Definitions ev[⇐]
  

  -- # Behavior

  proof-behavior : behavior src ⇔₂ behavior dst
  proof-behavior = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : behavior src ⊆₂' behavior dst
    ⊆-proof loc val (x , x∈src , x-w , x-val , x-loc , x-co-max) =
      ev[⇒] x∈src , events[⇒] x∈src , W[⇒] x∈src x-w , val[⇒] x∈src x-val , loc[⇒] x∈src x-loc , dst-x-co-max
      where
      dst-x-co-max : maximal (co dst) (ev[⇒] x∈src)
      dst-x-co-max (y , co[xy]) =
        let y∈dst = coʳ∈ex dst-wf co[xy]
        in x-co-max (ev[⇐] y∈dst , co[⇐$] x∈src (events[⇐] y∈dst) co[xy])

    ⊇-proof : behavior dst ⊆₂' behavior src
    ⊇-proof loc val (x , x∈dst , x-w , x-val , x-loc , x-co-max) =
      ev[⇐] x∈dst , events[⇐] x∈dst , W[⇐] x∈dst x-w , val[⇐] x∈dst x-val , loc[⇐] x∈dst x-loc , src-x-co-max
      where
      src-x-co-max : maximal (co src) (ev[⇐] x∈dst)
      src-x-co-max (y , co[xy]) =
        let y∈src = coʳ∈src co[xy]
        in x-co-max (ev[⇒] y∈src , co[⇒] (events[⇐] x∈dst) y∈src co[xy])
