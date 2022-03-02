{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder using (ReorderRestricted)


module Proof.Reorder.Single.WellFormed
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl) renaming (sym to ≡-sym)
open import Function using (_∘_; id)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂; swap)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Irreflexive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.LIMM
-- Local imports: Proof Components
open import Proof.Reorder.Single.Execution dst dst-res


open Execution
open IsLIMMConsistent
open WellFormed
open ReorderRestricted dst-res
open TransformReorder.Extra dst-res


--
-- Most Wellformedness properties are taken verbatim from the target,
-- /except/ those referencing `po`; Because we only modify `po`.
--


src-rmw-def : rmw src ⊆₂ po-imm src
src-rmw-def = ⊆: lemma
  where
  lemma : rmw src ⊆₂' po-imm src
  lemma x y rmw[xy]ˢ =
    let rmw[xy]ᵗ = rmw[xy]ˢ
        pi[xy]ᵗ = ⊆₂-apply (rmw-def dst-wf) rmw[xy]ᵗ
        
        ¬xy : ¬ (x ≡ ev₁ × y ≡ ev₂)
        ¬xy = λ{(x≡1 , y≡2) → ¬rmw₁ (take-udrˡ (rmw dst) (subst-rel (rmw src) x≡1 y≡2 rmw[xy]ˢ))}
        
        y≢ev₁ = λ{refl → ¬rmw₁ (take-udrʳ (rmw dst) rmw[xy]ˢ)}
        x≢ev₂ = λ{refl → ¬rmw₂ (take-udrˡ (rmw dst) rmw[xy]ˢ)}
    in pi[⇐] ¬xy y≢ev₁ x≢ev₂ pi[xy]ᵗ


src-po-init-first : ⊤-Precedes-⊥ EvInit (po src)
src-po-init-first {x} {y} po[xy] y-init =
  let y≢ev₁ = λ{refl → ¬init₁ y-init}
      dst-po[xy] = po[⇒]ʳ y≢ev₁ po[xy]
  in po-init-first dst-wf dst-po[xy] y-init


private
  po[21]ˢ : po src ev₂ ev₁
  po[21]ˢ = proj₁ pi[21]ˢ

  ¬po[12]ˢ : ¬ po src ev₁ ev₂
  ¬po[12]ˢ po[12] = src-po-irreflexive refl (src-po-trans po[12] po[21]ˢ)
  

src-po-tri : (tid : ThreadId) → Trichotomous _≡_ (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ events src) (po src))
src-po-tri tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src))
  with ev-eq-dec x ev₁ | ev-eq-dec y ev₂
... | yes refl | yes refl = tri> ¬po[12]ˢ (ev₁≢ev₂ ∘ with-pred-≡) po[21]ˢ
... | yes refl | no y≢2   =
  case po-tri dst-wf tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src)) of
  λ{ (tri<  po[xy] x≢y  ¬po[yx]) → tri< (po[⇐]ʳ y≢2 po[xy]) (λ{refl → ¬po[yx] po[xy]}) (¬po[⇐]ˡ y≢2 ¬po[yx])
   ; (tri≈ ¬po[xy] refl ¬po[yx]) → tri≈ (¬po[⇐]ˡ y≢2 ¬po[xy]) refl (¬po[⇐]ˡ y≢2 ¬po[yx])
   ; (tri> ¬po[xy] x≢y   po[yx]) →
       let y≢1 = λ{refl → ¬po[xy] po[yx]}
       in tri> (¬po[⇐]ʳ y≢1 ¬po[xy]) (λ{refl → ¬po[xy] po[yx]}) (po[⇐]ˡ y≢1 po[yx])
   }
... | no x≢1   | yes refl =
  case po-tri dst-wf tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src)) of
  λ{ (tri<  po[xy] x≢y  ¬po[yx]) → tri< (po[⇐]ˡ x≢1 po[xy]) (λ{refl → ¬po[yx] po[xy]}) (¬po[⇐]ʳ x≢1 ¬po[yx])
   ; (tri≈ ¬po[xy] refl ¬po[yx]) → tri≈ (¬po[⇐]ʳ x≢1 ¬po[yx]) refl (¬po[⇐]ʳ x≢1 ¬po[yx])
   ; (tri> ¬po[xy] x≢y   po[yx]) → 
       let x≢ev₂ = λ{refl → ¬po[xy] po[yx]}
       in tri> (¬po[⇐]ˡ x≢ev₂ ¬po[xy]) (λ{refl → ¬po[xy] po[yx]}) (po[⇐]ʳ x≢ev₂ po[yx])
   }
... | no x≢1   | no y≢2   =
  case po-tri dst-wf tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src)) of
  λ{ (tri<  po[xy] x≢y  ¬po[yx]) → tri< (po[⇐]ˡ x≢1 po[xy]) (λ{refl → ¬po[yx] po[xy]}) (¬po[⇐]ʳ x≢1 ¬po[yx])
   ; (tri≈ ¬po[xy] refl ¬po[yx]) → tri≈ (¬po[⇐]ʳ x≢1 ¬po[yx]) refl (¬po[⇐]ʳ x≢1 ¬po[yx])
   ; (tri> ¬po[xy] x≢y   po[yx]) →
       case₂ ev-eq-dec x ev₂ and ev-eq-dec y ev₁ of
       λ{ (yes refl) (yes refl) → tri< po[21]ˢ                 (λ{refl → ¬po[xy] po[yx]}) ¬po[12]ˢ
        ; (yes refl) (no y≢ev₁) → tri> (¬po[⇐]ʳ y≢ev₁ ¬po[xy]) (λ{refl → ¬po[xy] po[yx]}) (po[⇐]ˡ y≢ev₁ po[yx])
        ; (no x≢ev₂) _          → tri> (¬po[⇐]ˡ x≢ev₂ ¬po[xy]) (λ{refl → ¬po[xy] po[yx]}) (po[⇐]ʳ x≢ev₂ po[yx])
        }
   }


src-po-splittable : SplittableOrder (po src)
src-po-splittable = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : po src ⊆₂' TransClosure (po-imm src)
  ⊆-proof x y po[xy]ˢ with ×-dec (ev-eq-dec x ev₂) (ev-eq-dec y ev₁)
  ... | yes (refl , refl) = [ pi[21]ˢ ]
  ... | no ¬xy =
    let po[xy]ᵗ = po[⇒] ¬xy po[xy]ˢ
        pi⁺[xy]ᵗ = ⇔₂-apply-⊆₂ (po-splittable dst-wf) po[xy]ᵗ
    in pi⁺[⇐] (λ{(refl , refl) → ¬po[12]ˢ po[xy]ˢ}) pi⁺[xy]ᵗ

  ⊇-proof : TransClosure (po-imm src) ⊆₂' po src
  ⊇-proof x y pi⁺[xy] = ⁺-join-trans src-po-trans (⁺-map id proj₁ pi⁺[xy])


src-po-elements : udr (po src) ⇔₁ events src
src-po-elements = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : udr (po src) ⊆₁' events src
  ⊆-proof _ = ⇔₁-apply-⊆₁ (po-elements dst-wf) ∘ udr-po[⇒]

  ⊇-proof : events src ⊆₁' udr (po src)
  ⊇-proof _ = udr-po[⇐] ∘ ⇔₁-apply-⊇₁ (po-elements dst-wf)


src-po-stid : po src ⊆₂ ( ( EvInit ×₂ EvE ) ∪₂ SameTid )
src-po-stid = ⊆: lemma
  where
  lemma : po src ⊆₂' ( ( EvInit ×₂ EvE ) ∪₂ SameTid )
  lemma x y (po-new refl refl) =
    case ⊆₂-apply (po-stid dst-wf) po[12]ᵗ of
    λ{ (inj₁ (ev-init , _)) → ⊥-elim (¬init₁ ev-init)
     ; (inj₂ yx-stid) → inj₂ (sym-same-tid yx-stid)
     }
  lemma x y (po-dst ¬xy po[xy]) = ⊆₂-apply (po-stid dst-wf) po[xy]


src-wf : WellFormed src
src-wf =
  record
    { unique-ids     = unique-ids dst-wf
    ; events-unique  = events-unique dst-wf
    ; rmw-def        = src-rmw-def
    ; rmw-w          = rmw-w dst-wf
    ; rf-w×r         = rf-w×r dst-wf
    ; co-w×w         = co-w×w dst-wf
    ; rmw-r×w        = rmw-r×w dst-wf
    ; po-init-first  = src-po-init-first
    ; co-init-first  = co-init-first dst-wf
    ; po-tri         = src-po-tri
    ; co-tri         = co-tri dst-wf
    ; po-splittable  = src-po-splittable
    ; co-trans       = co-trans dst-wf
    ; events-uid-dec = events-uid-dec dst-wf
    ; rmwˡ-dec       = rmwˡ-dec dst-wf
    ; po-elements    = src-po-elements
    ; rf-elements    = rf-elements dst-wf
    ; co-elements    = co-elements dst-wf
    ; po-stid        = src-po-stid
    ; rf-sloc        = rf-sloc dst-wf
    ; co-sloc        = co-sloc dst-wf
    ; rmw-sloc       = rmw-sloc dst-wf
    ; rf-sval        = rf-sval dst-wf
    ; wf-rf-≥1       = wf-rf-≥1 dst-wf
    ; wf-rf-≤1       = wf-rf-≤1 dst-wf
    ; wf-init-≥1     = wf-init-≥1 dst-wf
    ; wf-init-≤1     = wf-init-≤1 dst-wf
    }
