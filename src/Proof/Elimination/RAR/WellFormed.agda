{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.LIMM using (LabelLIMM)
open import TransformRAR using (RAR-Restricted)


module Proof.Elimination.RAR.WellFormed
  (dst : Execution LabelLIMM)
  (dst-ok : RAR-Restricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Function using (_∘_; flip)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_; yes; no)
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
open import Proof.Elimination.RAR.Execution dst dst-ok as RAR-Ex


-- General Proof Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Elimination Proof Framework
open Δ.Definitions δ
open Δ.WellFormed δ
-- Other
open Ex.Execution
open Ex.WellFormed
open TransformRAR.Extra dst-ok
open RAR-Restricted dst-ok
open RAR-Ex.Extra


src-rf-w×r : rf src ⊆₂ EvW ×₂ EvR
src-rf-w×r = ⊆: lemma
  where
  lemma : rf src ⊆₂' EvW ×₂ EvR
  lemma _ _ rf[xy] = src-rfˡ-w rf[xy] , src-rfʳ-r rf[xy]

src-co-w×w : co src ⊆₂ EvW ×₂ EvW
src-co-w×w = ⊆: lemma
  where
  lemma : co src ⊆₂' EvW ×₂ EvW
  lemma _ _ co[xy] = src-coˡ-w co[xy] , src-coʳ-w co[xy]

src-co-init-first : ⊤-Precedes-⊥ EvInit (co src)
src-co-init-first (dst-x , dst-y , co[xy] , refl , refl) y-init =
  let x∈src = events[⇐] (coˡ∈ex dst-wf co[xy])
      y∈src = events[⇐] (coʳ∈ex dst-wf co[xy])
      dst-y-init = Init[⇒] y∈src y-init
      dst-x-init = co-init-first dst-wf co[xy] dst-y-init
  in Init[⇐$] x∈src dst-x-init

src-co-tri : (loc : Location) → Trichotomous _≡_ (filter-rel (EvW ∩₁ HasLoc loc ∩₁ events src) (co src))
src-co-tri loc (with-pred x (x-w , x-loc , x∈src)) (with-pred y (y-w , y-loc , y∈src))
  with co-tri dst-wf loc (with-pred (ev[⇒] x∈src) (W[⇒] ¬elim-x x∈src x-w , loc[⇒] ¬elim-x x∈src x-loc , events[⇒] x∈src)) (with-pred (ev[⇒] y∈src) (W[⇒] ¬elim-y y∈src y-w , loc[⇒] ¬elim-y y∈src y-loc , events[⇒] y∈src))
    where ¬elim-x = elim-¬w x-w
          ¬elim-y = elim-¬w y-w
... | tri<  co[xy] x≢y ¬co[yx] =
  tri< (co[⇐$] x∈src y∈src co[xy]) (λ{refl → x≢y refl}) (¬co[yx] ∘ co[⇒] (elim-¬w y-w) (elim-¬w x-w) y∈src x∈src)
... | tri≈ ¬co[xy] x≡y ¬co[yx] =
  tri≈ (¬co[xy] ∘ co[⇒] (elim-¬w x-w) (elim-¬w y-w) x∈src y∈src) lemma (¬co[yx] ∘ co[⇒] (elim-¬w y-w) (elim-¬w x-w) y∈src x∈src)
  where
  unique-pred : UniquePred (EvW ∩₁ HasLoc loc ∩₁ events src)
  unique-pred = ∩₁-unique-pred w-unique (∩₁-unique-pred has-loc-unique src-events-unique)
  lemma : with-pred x (x-w , x-loc , x∈src) ≡ with-pred y (y-w , y-loc , y∈src)
  lemma = with-pred-unique unique-pred (ev[⇐$]eq x∈src y∈src (with-pred-≡ x≡y)) (x-w , x-loc , x∈src) (y-w , y-loc , y∈src)
... | tri> ¬co[xy] x≢y  co[yx] =
  tri> (¬co[xy] ∘ co[⇒] (elim-¬w x-w) (elim-¬w y-w) x∈src y∈src) (λ{refl → x≢y refl}) (co[⇐$] y∈src x∈src co[yx])

src-co-trans : Transitive (co src)
src-co-trans co[xy] co[yz] =
  let x∈src = coˡ∈src co[xy]
      y∈src = coʳ∈src co[xy]
      z∈src = coʳ∈src co[yz]
      ¬elim-x = elim-¬w (src-coˡ-w co[xy])
      ¬elim-y = elim-¬w (src-coʳ-w co[xy])
      ¬elim-z = elim-¬w (src-coʳ-w co[yz])
      dst-co[xy] = co[⇒] ¬elim-x ¬elim-y x∈src y∈src co[xy]
      dst-co[yz] = co[⇒] ¬elim-y ¬elim-z y∈src z∈src co[yz]
      dst-co[xz] = co-trans dst-wf dst-co[xy] dst-co[yz]
  in co[⇐$] x∈src z∈src dst-co[xz]

src-rf-elements : udr (rf src) ⊆₁ events src
src-rf-elements = ⊆: (λ _ → udr-rf∈src)

src-co-elements : udr (co src) ⊆₁ events src
src-co-elements = ⊆: (λ _ → udr-co∈src)

src-rf-sloc : rf src ⊆₂ SameLoc
src-rf-sloc = ⊆: lemma
  where
  lemma : rf src ⊆₂' SameLoc
  lemma _ _ (rf-dst (_ , _ , dst-rf[xy] , refl , refl)) =
    let x∈dst = rfˡ∈ex dst-wf dst-rf[xy]
        y∈dst = rfʳ∈ex dst-wf dst-rf[xy]
        xy-sloc = ⊆₂-apply (rf-sloc dst-wf) dst-rf[xy]
    in sloc[⇐$] (events[⇐] x∈dst) (events[⇐] y∈dst) xy-sloc
  lemma _ _ (rf-new dst-rf[xp] refl refl) =
    let x∈dst = rfˡ∈ex dst-wf dst-rf[xp]
        xp-sloc = ⊆₂-apply (rf-sloc dst-wf) dst-rf[xp]
    in trans-same-loc
         (sloc[⇐$] (events[⇐] x∈dst) (events[⇐] preserved∈ex) xp-sloc)
         (subst-rel SameLoc src-preserved-def refl pe-sloc)

src-co-sloc : co src ⊆₂ SameLoc
src-co-sloc = ⊆: lemma
  where
  lemma : co src ⊆₂' SameLoc
  lemma x y co[xy] =
    let x∈src = coˡ∈src co[xy]
        y∈src = coʳ∈src co[xy]
        ¬elim-x = elim-¬w (×₂-applyˡ src-co-w×w co[xy])
        ¬elim-y = elim-¬w (×₂-applyʳ src-co-w×w co[xy])
        dst-co[xy] = co[⇒] ¬elim-x ¬elim-y x∈src y∈src co[xy]
        xy-sloc = ⊆₂-apply (co-sloc dst-wf) dst-co[xy]
    in sloc[⇐$] x∈src y∈src xy-sloc


src-rf-sval : rf src ⊆₂ SameVal
src-rf-sval = ⊆: lemma
  where
  lemma : rf src ⊆₂' SameVal
  lemma _ _ (rf-dst (_ , _ , dst-rf[xy] , refl , refl)) =
    let x∈dst = rfˡ∈ex dst-wf dst-rf[xy]
        y∈dst = rfʳ∈ex dst-wf dst-rf[xy]
        xy-sval = ⊆₂-apply (rf-sval dst-wf) dst-rf[xy]
    in sval[⇐$] (events[⇐] x∈dst) (events[⇐] y∈dst) xy-sval
  lemma _ _ (rf-new dst-rf[xp] refl refl) =
    let x∈dst = rfˡ∈ex dst-wf dst-rf[xp]
        xy-sval = ⊆₂-apply (rf-sval dst-wf) dst-rf[xp]
    in trans-same-val (sval[⇐$] (events[⇐] x∈dst) (events[⇐] preserved∈ex) xy-sval) (subst-rel SameVal src-preserved-def refl pe-sval)


src-wf-rf-≥1 : (EvR ∩₁ events src) ⊆₁ codom (rf src)
src-wf-rf-≥1 = ⊆: lemma
  where
  lemma : (EvR ∩₁ events src) ⊆₁' codom (rf src)
  lemma x (x-r , x∈src) with ev-eq-dec x src-elim-ev
  ... | yes refl =
    let (y , rf[yp]) = ⊆₁-apply (wf-rf-≥1 dst-wf) (rₜ⇒r preserved-ev-r , preserved∈ex)
        y∈dst = rfˡ∈ex dst-wf rf[yp]
    in ev[⇐] y∈dst , rf-new rf[yp] refl refl
  ... | no ¬x-elim =
    let dst-x-r = R[⇒] ¬x-elim x∈src x-r
        x∈dst = events[⇒] x∈src
        (y , rf[yx]) = ⊆₁-apply (wf-rf-≥1 dst-wf) (dst-x-r , x∈dst)
        y∈dst = rfˡ∈ex dst-wf rf[yx]
    in ev[⇐] y∈dst , rf[⇐$] (events[⇐] y∈dst) x∈src rf[yx]


src-wf-rf-≤1 : Functional _≡_ (flip (rf src))
src-wf-rf-≤1 x y₁ y₂ rf[y₁x] rf[y₂x] with ev-eq-dec x src-elim-ev
... | yes refl =
  let y₁∈src = rfˡ∈src rf[y₁x]
      y₂∈src = rfˡ∈src rf[y₂x]
      ¬elim-y₁ = elim-¬w (×₂-applyˡ src-rf-w×r rf[y₁x])
      ¬elim-y₂ = elim-¬w (×₂-applyˡ src-rf-w×r rf[y₂x])
      dst-rf[y₁p] = rf[⇒] ¬elim-y₁ ¬elim-pres-src y₁∈src preserved∈src (rfʳ-e⇒p rf[y₁x])
      dst-rf[y₂p] = rf[⇒] ¬elim-y₂ ¬elim-pres-src y₂∈src preserved∈src (rfʳ-e⇒p rf[y₂x])
      dst-y₁≡y₂ = wf-rf-≤1 dst-wf _ _ _ dst-rf[y₁p] dst-rf[y₂p]
  in ev[⇐$]eq y₁∈src y₂∈src dst-y₁≡y₂
... | no ¬elim-x =
  let x∈src = rfʳ∈src rf[y₁x]
      y₁∈src = rfˡ∈src rf[y₁x]
      y₂∈src = rfˡ∈src rf[y₂x]
      ¬elim-y₁ = elim-¬w (×₂-applyˡ src-rf-w×r rf[y₁x])
      ¬elim-y₂ = elim-¬w (×₂-applyˡ src-rf-w×r rf[y₂x])
      dst-rf[y₁x] = rf[⇒] ¬elim-y₁ ¬elim-x y₁∈src x∈src rf[y₁x]
      dst-rf[y₂x] = rf[⇒] ¬elim-y₂ ¬elim-x y₂∈src x∈src rf[y₂x]
      dst-y₁≡y₂ = wf-rf-≤1 dst-wf _ _ _ dst-rf[y₁x] dst-rf[y₂x]
  in ev[⇐$]eq y₁∈src y₂∈src dst-y₁≡y₂

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
