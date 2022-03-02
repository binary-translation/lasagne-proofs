{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder12 using (ReorderRestricted12)


module Proof.Reorder.Reorder12.Consistent
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted12 dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Function using (_∘_; id)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Irreflexive)
-- Library imports
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.LIMM
open import Arch.LIMM.Detour
-- Local imports: Proof Components
open import Proof.Reorder.Reorder12.Execution dst dst-res
open import Proof.Reorder.Reorder12.WellFormed dst dst-res


open Execution
open IsLIMMConsistent
open ReorderRestricted12 dst-res


src-ax-coherence : Acyclic _≡_ (Coh src)
src-ax-coherence {x} refl = ax-coherence dst-ok refl ∘ ⁺-map (λ τ → τ) coh[⇒]
  where
  coh[⇒] : {x y : Event LabelLIMM} → Coh src x y → Coh dst x y
  coh[⇒] {x} {y} (coh-po-loc (po[xy] , xy-sloc@(same-loc x-loc _))) =
    let x≢3 = λ{refl → ¬f-loc ev₃-f (_ , x-loc)}
    in coh-po-loc (po[⇒]ˡ x≢3 po[xy] , xy-sloc)
  coh[⇒] (coh-rf rf[xy]) = coh-rf rf[xy]
  coh[⇒] (coh-fr fr[xy]) = coh-fr fr[xy]
  coh[⇒] (coh-co co[xy]) = coh-co co[xy]


src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  ax-atomicity dst-ok x y (rmw[xy] , fre[⇒] fre[xz] ⨾[ z ]⨾ coe[⇒] coe[zy])


src-ax-global-ord : Irreflexive _≡_ (ghb src)
src-ax-global-ord refl ghb[xx] = 
  let -- If there exists a GHB cycle in the source, then there exists a detour cycle
      -- which necessarily goes between R/W events
      (z , src-ghb-alt[zz]) = detour src-wf ghb[xx]
      -- If there exists a detour cycle in the source, there exists one in the target
      dst-ghb-alt[zz] = ⁺-map id ghbi[⇒] src-ghb-alt[zz]
      -- If there exists a detour cycle in the target, there exists a regular cycle
      dst-ghb[zz] = GhbiAlt⁺⇒Ghbi⁺ dst-ghb-alt[zz]
      -- As no such cycle may exist in the target, the original cycle may not exist in the source
  in ax-global-ord dst-ok refl dst-ghb[zz]


src-consistent : IsLIMMConsistent src
src-consistent =
  record {
    ax-coherence  = src-ax-coherence
  ; ax-atomicity  = src-ax-atomicity
  ; ax-global-ord = src-ax-global-ord
  }
