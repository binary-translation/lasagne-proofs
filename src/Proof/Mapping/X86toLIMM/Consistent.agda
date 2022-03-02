{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import MapX86toLIMM using (LIMM-X86Restricted)


module Proof.Mapping.X86toLIMM.Consistent
  (dst : Execution LabelLIMM) (dst-wf : WellFormed dst) (dst-ok : LIMM-X86Restricted dst) where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_])
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.LIMM as LIMM
open import Arch.X86 as X86
open import Helpers

open import MapX86toLIMM
open import Proof.Mapping.X86toLIMM.Execution dst dst-wf dst-ok as PE

import Proof.Framework LabelX86 dst dst-wf as Ψ
import Proof.Mapping.Framework LabelX86 dst dst-wf as Δ

open Execution
open WellFormed
open IsLIMMConsistent
open LIMM-X86Restricted
open PE.Extra



-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result: Consistent


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ
  

-- # Definitions

private
  dst-consistent = consistent dst-ok
  

-- # Proof: Coherence

src-ax-coherence : Acyclic _≡_ ( po-loc src ∪₂ rf src ∪₂ fr src ∪₂ co src )
src-ax-coherence refl coh[xx] =
  let x∈src = ⁺-lift-predˡ cohˡ∈src coh[xx]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ cohˡ∈src coh[⇒] x∈src x∈src coh[xx])
  where
  cohˡ∈src : ∀ {x y : Event LabelX86} → ( po-loc src ∪₂ rf src ∪₂ fr src ∪₂ co src ) x y → x ∈ events src
  cohˡ∈src (inj₁ (inj₁ (inj₁ po-loc[xy]))) = poˡ∈src (proj₁ po-loc[xy])
  cohˡ∈src (inj₁ (inj₁ (inj₂ rf[xy])))     = rfˡ∈src rf[xy]
  cohˡ∈src (inj₁ (inj₂ fr[xy]))            = frˡ∈src fr[xy]
  cohˡ∈src (inj₂ co[xy])                   = coˡ∈src co[xy]
  
  coh[⇒] : Rel[⇒] ( po-loc src ∪₂ rf src ∪₂ fr src ∪₂ co src ) (Coh dst)
  coh[⇒] x∈src y∈src (inj₁ (inj₁ (inj₁ po-loc[xy]))) = coh-po-loc (po-loc[⇒] x∈src y∈src po-loc[xy])
  coh[⇒] x∈src y∈src (inj₁ (inj₁ (inj₂ rf[xy])))     = coh-rf (rf[⇒] x∈src y∈src rf[xy])
  coh[⇒] x∈src y∈src (inj₁ (inj₂ fr[xy]))            = coh-fr (fr[⇒] x∈src y∈src fr[xy])
  coh[⇒] x∈src y∈src (inj₂ co[xy])                   = coh-co (co[⇒] x∈src y∈src co[xy])


-- # Proof: Atomicity

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
  in
  ax-atomicity dst-consistent (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] x∈src z∈src fre[xz] ⨾[ _ ]⨾ coe[⇒] z∈src y∈src coe[zy]
    )


-- # Proof: Global Order

private
  -- | Like `Xhb`, but rfi/fri/coi are extracted and placed into `xppo`.
  data XhbAlt (ex : Execution LabelX86) (x y : Event LabelX86) : Set where
    xhba-init    : ( ⦗ EvInit ⦘ ⨾ po ex ) x y → XhbAlt ex x y
    xhba-xppo    : Xppo ex x y → XhbAlt ex x y
    xhba-implied : Implied ex x y → XhbAlt ex x y
    xhba-rfe     : rfe ex x y → XhbAlt ex x y
    xhba-fre     : fre ex x y → XhbAlt ex x y
    xhba-coe     : coe ex x y → XhbAlt ex x y
    
  -- Intuitively, we extract: rf = rfi ∪₂ rfe , co = coi ∪₂ coe , fr = fri ∪₂ fre
  -- Then: rfi ∪₂ fri ∪₂ coi ⊆ xppo
  xhb-alt : {ex : Execution LabelX86} → WellFormed ex → (x y : Event LabelX86) → Xhb ex x y → XhbAlt ex x y
  xhb-alt wf x y (xhb-init init[xy]) = xhba-init init[xy]
  xhb-alt wf x y (xhb-xppo xppo[xy]) = xhba-xppo xppo[xy]
  xhb-alt wf x y (xhb-implied implied[xy]) = xhba-implied implied[xy]
  xhb-alt wf x y (xhb-rfe rfe[xy]) = xhba-rfe rfe[xy]
  xhb-alt wf x y (xhb-fr fr[xy]) with ⇔₂-apply-⊆₂ (internal⊎external fr wf) fr[xy]
  xhb-alt wf x y (xhb-fr fr[xy]) | inj₂ fre[xy] = xhba-fre fre[xy]
  xhb-alt wf x y (xhb-fr fr[xy]) | inj₁ fri[xy]@(_ , po[xy]) with ⊆₂-apply (fr-r×w wf) fr[xy]
  xhb-alt wf x y (xhb-fr fr[xy]) | inj₁ (_ , po[xy]) | ev-r is-lab-r , ev-init with po-init-first wf po[xy] ev-init
  xhb-alt wf x y (xhb-fr fr[xy]) | inj₁ (_ , po[xy]) | ev-r is-lab-r , ev-init | ()
  xhb-alt wf x y (xhb-fr fr[xy]) | inj₁ (_ , po[xy]) | ev-r is-rt , ev-w is-wt =
    xhba-xppo (xppo-r×w ((ev-r is-rt , ev-w is-wt) , po[xy]))
  xhb-alt wf x y (xhb-co co[xy]) with ⇔₂-apply-⊆₂ (internal⊎external co wf) co[xy]
  xhb-alt wf x y (xhb-co co[xy]) | inj₂ coe[xy] = xhba-coe coe[xy]
  xhb-alt wf x y (xhb-co co[xy]) | inj₁ coi[xy]@(_ , po[xy]) =
    let xppo[xy] = xppo-w×w (⊆₂-apply (co-w×w wf) {x = x} {y = y} co[xy] , po[xy])
    in xhba-xppo xppo[xy]

src-ax-ghb : Acyclic _≡_ (Xhb src)
src-ax-ghb = acyclic-⊆₂ proof-alt (⊆: (xhb-alt src-wf))
  where
  -- # xppo
  xppo[⇒]ord : Rel[⇒] (Xppo src) (Ord dst)
  -- ## R × W
  xppo[⇒]ord {_} {.(event-init _ _ _)} x∈src y∈src (xppo-r×w ((ev-r is-r , ev-init) , po[xy])) =
    absurd (po-init-first src-wf po[xy] ev-init) λ()
  xppo[⇒]ord {x@(event _ _ (lab-r tmov _ _))} {y@(event _ _ (lab-w tmov _ _))} x∈src y∈src (xppo-r×w ((ev-r is-r , ev-w is-w) , po[xy])) =
    ord-rm lemma
    where
    lemma : ( ⦗ EvR ⦘ ⨾ po dst ⨾ ⦗ EvF₌ RM ⦘ ⨾ po dst ⨾ ⦗ EvRW ⦘ ) (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
    lemma with splitˡ (po-splittable dst-wf) (po[⇒] x∈src y∈src po[xy])
    lemma | inj₁ pi[xy] with r-f-po₁ dst-ok (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r is-r refl))
    lemma | inj₁ pi[xy] | z , pi[xz] , z-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xy] pi[xz]
    lemma | inj₁ pi[xy] | z , pi[xz] , z-is-f | refl = ⊥-elim (disjoint-f/w z (f₌⇒f z-is-f , W[⇒] y∈src (ev-w is-w)))
    lemma | inj₂ (z  , pi[xz] , po[zy]) with r-f-po₁ dst-ok (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r is-r refl))
    lemma | inj₂ (z  , pi[xz] , po[zy]) | w , pi[xw] , w-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xw] pi[xz]
    lemma | inj₂ (.w , pi[xw] , po[wy]) | w , _ , w-is-f | refl =
      (refl , R[⇒] x∈src (ev-r is-r)) ⨾[ _ ]⨾ proj₁ pi[xw] ⨾[ _ ]⨾ (refl , w-is-f) ⨾[ w ]⨾ po[wy] ⨾[ _ ]⨾ (refl , RW[⇒] y∈src (ev-w is-w))
  xppo[⇒]ord {x@(event _ _ (lab-r tmov _ _))} {y@(event _ _ (lab-w trmw _ _))} x∈src y∈src (xppo-r×w ((ev-r is-r , ev-w is-w) , po[xy])) =
    ord-w (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , Wₜ[⇒] y∈src (ev-w is-w refl)))
  xppo[⇒]ord {x@(event _ _ (lab-r trmw _ _))} {y@(event _ _ (lab-w _ _ _))} x∈src y∈src (xppo-r×w ((ev-r is-r , ev-w is-w) , po[xy])) =
    ord-r ((refl , Rₜ[⇒] x∈src (ev-r is-r refl)) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])
  -- ## W × W
  xppo[⇒]ord {x@(event-init _ _ _)} {y} x∈src y∈src (xppo-w×w ((ev-init , y-is-w) , po[xy])) =
    ord-init ((refl , Init[⇒] x∈src ev-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])
  xppo[⇒]ord {.(event _ _ (lab-w _ _ _))} {.(event-init _ _ _)} x∈src y∈src (xppo-w×w ((ev-w is-w , ev-init) , po[xy])) = 
    absurd (po-init-first src-wf po[xy] ev-init) λ()
  xppo[⇒]ord {x@(event _ _ (lab-w _ _ _))} {y@(event _ _ (lab-w tmov _ _))} x∈src y∈src (xppo-w×w ((ev-w is-w , ev-w is-w) , po[xy])) =
    ord-ww lemma
    where
    lemma : ( ⦗ EvW ⦘  ⨾ po dst ⨾ ⦗ EvF₌ WW ⦘ ⨾ po dst ⨾ ⦗ EvW ⦘ ) (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
    lemma with splitʳ (po-splittable dst-wf) (po[⇒] x∈src y∈src po[xy]) |  f-w-po₁ dst-ok {ev[⇒] y∈src} (events[⇒] y∈src) (Wₜ[⇒] y∈src (ev-w is-w refl))
    lemma | inj₁ pi[xy] | z , pi[zy] , z-is-f with po-immˡ dst-wf pi[zy] pi[xy]
    lemma | inj₁ pi[xy] | z , pi[zy] , z-is-f | refl = ⊥-elim (disjoint-f/w _ (f₌⇒f z-is-f , W[⇒] x∈src (ev-w is-w)))
    lemma | inj₂ (z , po[xz] , pi[zy]) | w , pi[wy] , w-is-f with po-immˡ dst-wf pi[zy] pi[wy]
    lemma | inj₂ (.w , po[xz] , pi[zy]) | w , pi[wy] , w-is-f | refl =
      (refl , W[⇒] x∈src (ev-w is-w)) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , w-is-f) ⨾[ w ]⨾ proj₁ pi[wy] ⨾[ _ ]⨾ (refl , W[⇒] y∈src (ev-w is-w))
  xppo[⇒]ord {x@(event _ _ (lab-w _ _ _))} {y@(event _ _ (lab-w trmw _ _))} x∈src y∈src (xppo-w×w ((ev-w is-w , ev-w is-w) , po[xy])) =
    ord-w (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , Wₜ[⇒] y∈src (ev-w is-w refl)))
  -- ## R × R
  xppo[⇒]ord {x@(event _ _ (lab-r tmov _ _))} {y@(event _ _ (lab-r _ _ _))} x∈src y∈src (xppo-r×r ((ev-r is-r , ev-r is-r) , po[xy])) =
    ord-rm lemma
    where
    lemma : ( ⦗ EvR ⦘ ⨾ po dst ⨾ ⦗ EvF₌ RM ⦘ ⨾ po dst ⨾ ⦗ EvRW ⦘ ) (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
    lemma with splitˡ (po-splittable dst-wf) (po[⇒] x∈src y∈src po[xy])
    lemma | inj₁ pi[xy] with r-f-po₁ dst-ok (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r is-r refl))
    lemma | inj₁ pi[xy] | z , pi[xz] , z-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xy] pi[xz]
    lemma | inj₁ pi[xy] | _ , pi[xz] , z-is-f | refl = ⊥-elim (disjoint-f/r _ (f₌⇒f z-is-f , R[⇒] y∈src (ev-r is-r)))
    lemma | inj₂ (z , pi[xz] , po[zy]) with r-f-po₁ dst-ok (events[⇒] x∈src) (Rₜ[⇒] x∈src (ev-r is-r refl))
    lemma | inj₂ (z , pi[xz] , po[zy]) | w , pi[xw] , w-is-f with po-immʳ dst-wf (¬Init[⇒] x∈src (λ())) pi[xw] pi[xz]
    lemma | inj₂ (.w , pi[xw] , po[wy]) | w , _ , w-is-f | refl =
      (refl , R[⇒] x∈src (ev-r is-r)) ⨾[ ev[⇒] {x} x∈src ]⨾ proj₁ pi[xw] ⨾[ w ]⨾ (refl , w-is-f) ⨾[ w ]⨾ po[wy] ⨾[ ev[⇒] {y} y∈src ]⨾ (refl , RW[⇒] y∈src (ev-r is-r))
  xppo[⇒]ord {x@(event _ _ (lab-r trmw _ _))} {y@(event _ _ (lab-r _ _ _))} x∈src y∈src (xppo-r×r ((ev-r is-r , ev-r is-r) , po[xy])) =
    ord-r ((refl , Rₜ[⇒] x∈src (ev-r is-r refl)) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])


  implied[⇒]ord : Rel[⇒] (Implied src) (Ord dst)
  implied[⇒]ord {x} {y} x∈src y∈src (implied-pof (po[xy] ⨾[ y ]⨾ (refl , inj₁ y∈rmwdom@(z , rmw[yz])))) =
    let z∈src = rmwʳ∈src rmw[yz]
    in ord-rmw-dom (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , ev[⇒] {z} z∈src , rmw[⇒] y∈src z∈src rmw[yz]))
  implied[⇒]ord {x} {y} x∈src y∈src (implied-pof (⨾: .(event _ _ lab-f) po[xy] (refl , inj₂ (ev-f is-f)))) =
    ord-sc₁ (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , F[⇒] y∈src (ev-f is-f)))
  implied[⇒]ord {x} {y} x∈src y∈src (implied-fpo ((refl , inj₁ x∈rmwcodom@(z , rmw[zx])) ⨾[ x ]⨾ po[xy])) =
    let z∈src = rmwˡ∈src rmw[zx]
    in ord-rmw-codom ((refl , (_ , rmw[⇒] z∈src x∈src rmw[zx])) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])
  implied[⇒]ord {x} {y} x∈src y∈src (implied-fpo ((refl , inj₂ x-is-f) ⨾[ x ]⨾ po[xy])) =
    ord-sc₂ ((refl , F[⇒] x∈src x-is-f) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])


  xhba[⇒]ghbi : Rel[⇒] (XhbAlt src) (Ghbi dst)
  xhba[⇒]ghbi x∈src y∈src (xhba-init ((refl , x-init) ⨾[ _ ]⨾ po[xy])) =
    ghbi-ord (ord-init ((refl , Init[⇒] x∈src x-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy]))
  xhba[⇒]ghbi x∈src y∈src (xhba-xppo xppo[xy])       = ghbi-ord (xppo[⇒]ord x∈src y∈src xppo[xy])
  xhba[⇒]ghbi x∈src y∈src (xhba-implied implied[xy]) = ghbi-ord (implied[⇒]ord x∈src y∈src implied[xy])
  xhba[⇒]ghbi x∈src y∈src (xhba-rfe rfe[xy])         = ghbi-rfe (rfe[⇒] x∈src y∈src rfe[xy])
  xhba[⇒]ghbi x∈src y∈src (xhba-fre fre[xy])         = ghbi-fre (fre[⇒] x∈src y∈src fre[xy])
  xhba[⇒]ghbi x∈src y∈src (xhba-coe coe[xy])         = ghbi-coe (coe[⇒] x∈src y∈src coe[xy])


  xhbaˡ∈src : ∀ {x y : Event LabelX86} → XhbAlt src x y → x ∈ events src
  xhbaˡ∈src (xhba-init ((refl , x-init) ⨾[ _ ]⨾ po[xy])) = poˡ∈src po[xy]
  xhbaˡ∈src (xhba-xppo xppo[xy])       = poˡ∈src (xppo⇒po xppo[xy])
  xhbaˡ∈src (xhba-implied implied[xy]) = poˡ∈src (implied⇒po implied[xy])
  xhbaˡ∈src (xhba-rfe (rf[xy] , _))    = rfˡ∈src rf[xy]
  xhbaˡ∈src (xhba-fre (fr[xy] , _))    = frˡ∈src fr[xy]
  xhbaˡ∈src (xhba-coe (co[xy] , _))    = coˡ∈src co[xy]


  proof-alt : Acyclic _≡_ (XhbAlt src)
  proof-alt refl xhb⁺xx = 
    let x∈src = ⁺-lift-predˡ xhbaˡ∈src xhb⁺xx
    in ax-global-ord dst-consistent refl (⁺[⇒]ˡ xhbaˡ∈src xhba[⇒]ghbi x∈src x∈src xhb⁺xx)
    

-- # Result: Consistent

src-consistent : IsX86Consistent src
src-consistent =
  record
    { ax-coherence = src-ax-coherence
    ; ax-atomicity = src-ax-atomicity
    ; ax-ghb       = src-ax-ghb
    }
