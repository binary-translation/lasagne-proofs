{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.X86 using (LabelX86)
open import MapLIMMtoX86 using (X86-LIMMRestricted)


module Proof.Mapping.LIMMtoX86.Consistent
  (dst : Execution LabelX86)
  (dst-wf : WellFormed dst)
  (dst-ok : X86-LIMMRestricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary using (Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_])
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.LIMM as LIMM
open import Arch.LIMM.Detour
open import Arch.X86 as X86
-- Local imports: Theorem Specification
open import MapLIMMtoX86
-- Local imports: Proof Components
import Proof.Framework LabelLIMM dst dst-wf as Ψ
import Proof.Mapping.Framework LabelLIMM dst dst-wf as Δ
open import Proof.Mapping.LIMMtoX86.Execution dst dst-wf dst-ok as PE


open Execution
open WellFormed
open IsX86Consistent
open X86-LIMMRestricted dst-ok
open PE.Extra


-- -- File structure
-- -- * Definitions
-- -- * Proof: Coherence
-- -- * Proof: Atomicity
-- -- * Proof: Global Order
-- -- * Result


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ


private
  dst-consistent = consistent


-- # Proof: Coherence

src-ax-coherence  : Acyclic _≡_ ( Coh src )
src-ax-coherence refl coh[xx] =
  let x∈src = ⁺-lift-predˡ (cohˡ∈ex src-wf) coh[xx]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ (cohˡ∈ex src-wf) coh[⇒] x∈src x∈src coh[xx])
  where
  coh[⇒] : Rel[⇒] (Coh src) (po-loc dst ∪₂ rf dst ∪₂ fr dst ∪₂ co dst)
  coh[⇒] x∈src y∈src (coh-po-loc po-loc[xy]) = inj₁ (inj₁ (inj₁ (po-loc[⇒] x∈src y∈src po-loc[xy])))
  coh[⇒] x∈src y∈src (coh-rf rf[xy])         = inj₁ (inj₁ (inj₂ (rf[⇒] x∈src y∈src rf[xy])))
  coh[⇒] x∈src y∈src (coh-fr fr[xy])         = inj₁ (inj₂ (fr[⇒] x∈src y∈src fr[xy]))
  coh[⇒] x∈src y∈src (coh-co co[xy])         = inj₂ (co[⇒] x∈src y∈src co[xy])


-- # Proof: Atomicity

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
  in
  ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] x∈src z∈src fre[xz] ⨾[ ev[⇒] z∈src ]⨾ coe[⇒] z∈src y∈src coe[zy]
    )


-- # Proof: Global Order

src-ax-global-ord : Irreflexive _≡_ (ghb src)
src-ax-global-ord refl ghb[xx] =
  let (z , ghbd[zz]) = detour src-wf ghb[xx]
      z∈src = ⁺-lift-predˡ (GhbiAltˡ∈ex src-wf) ghbd[zz]
      xhb⁺⁺[zz] = ⁺[⇒]ˡ (GhbiAltˡ∈ex src-wf) ghbi[⇒]xhb z∈src z∈src ghbd[zz]
      xhb⁺[zz] = ⁺-join xhb⁺⁺[zz]
  in ax-ghb dst-consistent refl xhb⁺[zz]
  where
  ord[⇒]xhb : Rel[⇒] (OrdAlt src) (TransClosure (Xhb dst))
  ord[⇒]xhb x∈src y∈src (ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    [ xhb-init ((refl , Init[⇒] x∈src ev-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy]) ]
  ord[⇒]xhb x∈src y∈src (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw)))
    with rw/rw y-rw
  ... | inj₁ y-r =
    [ xhb-xppo (xppo-r×r ((R[⇒] x∈src x-r , R[⇒] y∈src y-r) , po[⇒] x∈src y∈src (po-trans src-wf po[xz] po[zy]))) ]
  ... | inj₂ y-w =
    [ xhb-xppo (xppo-r×w ((R[⇒] x∈src x-r , W[⇒] y∈src y-w) , po[⇒] x∈src y∈src (po-trans src-wf po[xz] po[zy]))) ]
  ord[⇒]xhb x∈src y∈src (ord-ww ((refl , x-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-ww) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-w))) =
    [ xhb-xppo (xppo-w×w ((W[⇒] x∈src x-w , W[⇒] y∈src y-w) , po[⇒] x∈src y∈src (po-trans src-wf po[xz] po[zy]))) ]
  ord[⇒]xhb x∈src y∈src (ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw))) =
    let z∈src = poʳ∈ex src-wf po[xz]
        zᵗ-f = F[⇒] z∈src z-sc
    in xhb-implied (implied-pof (po[⇒] x∈src z∈src po[xz] ⨾[ _ ]⨾ (refl , inj₂ zᵗ-f)))
         ∷ [ xhb-implied (implied-fpo ((refl , inj₂ zᵗ-f) ⨾[ _ ]⨾ po[⇒] z∈src y∈src po[zy])) ]
  ord[⇒]xhb x∈src y∈src (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ))) =
    [ xhb-implied (implied-pof (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , (inj₁ (rmwˡ[⇒] y∈src y∈rmwˡ))))) ]
  ord[⇒]xhb x∈src y∈src (ord-rmw-codom ((refl , x-rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
    [ xhb-implied (implied-fpo ((refl , inj₁ (rmwʳ[⇒] x∈src x-rmwʳ)) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])) ]
  ord[⇒]xhb x∈src y∈src (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-wₜ)))
    with rw/rw x-rw
  ... | inj₁ x-r =
    [ xhb-xppo (xppo-r×w ((R[⇒] x∈src x-r , W[⇒] y∈src (wₜ⇒w y-wₜ)) , po[⇒] x∈src y∈src po[xy])) ]
  ... | inj₂ x-w =
    [ xhb-xppo (xppo-w×w ((W[⇒] x∈src x-w , W[⇒] y∈src (wₜ⇒w y-wₜ)) , po[⇒] x∈src y∈src po[xy])) ]
  ord[⇒]xhb x∈src y∈src (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)))
    with rw/rw y-rw
  ... | inj₁ y-r =
    [ xhb-xppo (xppo-r×r ((R[⇒] x∈src (rₜ⇒r x-rₜ) , R[⇒] y∈src y-r) , po[⇒] x∈src y∈src po[xy])) ]
  ... | inj₂ y-w =
    [ xhb-xppo (xppo-r×w ((R[⇒] x∈src (rₜ⇒r x-rₜ) , W[⇒] y∈src y-w) , po[⇒] x∈src y∈src po[xy])) ]
  
  ghbi[⇒]xhb : Rel[⇒] (GhbiAlt src) (TransClosure (Xhb dst))
  ghbi[⇒]xhb x∈src y∈src (ghbi-ord ord[xy]) = ord[⇒]xhb x∈src y∈src ord[xy]
  ghbi[⇒]xhb x∈src y∈src (ghbi-rfe rfe[xy]) = [ xhb-rfe (rfe[⇒] x∈src y∈src rfe[xy]) ]
  ghbi[⇒]xhb x∈src y∈src (ghbi-coe coe[xy]) = [ xhb-co (co[⇒] x∈src y∈src (proj₁ coe[xy])) ]
  ghbi[⇒]xhb x∈src y∈src (ghbi-fre fre[xy]) = [ xhb-fr (fr[⇒] x∈src y∈src (proj₁ fre[xy])) ]


-- # Result

src-consistent : IsLIMMConsistent src
src-consistent =
  record
    { ax-coherence  = src-ax-coherence
    ; ax-atomicity  = src-ax-atomicity
    ; ax-global-ord = src-ax-global-ord
    }
