{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder21 using (ReorderRestricted21)


module Proof.Reorder.Reorder21.WellFormed
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted21 dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
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
open import Arch.General.DerivedWellformed
open import Arch.LIMM
open import Arch.LIMM.Detour
-- Local imports: Proof Components
open import Proof.Reorder.Reorder21.Execution dst dst-res


open Execution
open IsLIMMConsistent
open WellFormed
open ReorderRestricted21 dst-res
open TransformReorder21.Extra dst-res


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
        x-r = rₜ⇒r (rmwˡ-r dst-wf (_ , rmw[xy]ˢ))
        y-w = wₜ⇒w (rmwʳ-w dst-wf (_ , rmw[xy]ˢ))
        x≢1 = λ{x≡1 → disjoint-f/r _ (ev₁-f , subst EvR x≡1 x-r)}
        y≢1 = λ{y≡1 → disjoint-f/w _ (ev₁-f , subst EvW y≡1 y-w)}
        x≢3 = λ{x≡3 → disjoint-r/w _ (subst EvR x≡3 x-r , ev₃-w)}
    in pi[⇐] (x≢1 ∘ proj₁) (x≢1 ∘ proj₁) y≢1 x≢3 pi[xy]ᵗ


src-po-init-first : ⊤-Precedes-⊥ EvInit (po src)
src-po-init-first {x} {y} po[xy] y-init =
  let y≢ev₁ = λ{refl → ¬init₁ y-init}
      dst-po[xy] = po[⇒]ʳ y≢ev₁ po[xy]
  in po-init-first dst-wf dst-po[xy] y-init


private

  ¬po₁₁ˢ : ¬ po src ev₁ ev₁
  ¬po₁₁ˢ = src-po-irreflexive refl
  
  ¬po₁₂ˢ : ¬ po src ev₁ ev₂
  ¬po₁₂ˢ po[12] = ¬po₁₁ˢ (src-po-trans po[12] po₂₁ˢ)
  
  ¬po₁₃ˢ : ¬ po src ev₁ ev₃
  ¬po₁₃ˢ po[13] = ¬po₁₁ˢ (src-po-trans po[13] po₃₁ˢ)
  

src-po-tri : (tid : ThreadId) → Trichotomous _≡_ (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ events src) (po src))
src-po-tri tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src))
  with po-tri dst-wf tid (with-pred x (x-init/tid , x∈src)) (with-pred y (y-init/tid , y∈src))
... | tri<  po[xy]ᵗ x≢y  ¬po[yx]ᵗ =
  case ×-dec (ev-eq-dec x ev₁) (ev-eq-dec y ev₃) of
  λ{ (yes (refl , refl)) →
       tri> ¬po₁₃ˢ (ev₁≢ev₃ ∘ with-pred-≡) po₃₁ˢ
   ; (no ¬13) →
       case ×-dec (ev-eq-dec x ev₁) (ev-eq-dec y ev₂) of
       λ{ (yes (refl , refl)) → tri> ¬po₁₂ˢ (ev₁≢ev₂ ∘ with-pred-≡) po₂₁ˢ
        ; (no ¬12) → tri< (po[⇐] ¬12 ¬13 po[xy]ᵗ) (λ{refl → ¬po[yx]ᵗ po[xy]ᵗ}) (¬po[⇐] (¬12 ∘ swap) (¬13 ∘ swap) ¬po[yx]ᵗ)
        }
   }
... | tri≈ ¬po[xy]ᵗ refl ¬po[yx]ᵗ =
  tri≈ (src-po-irreflexive refl) refl (src-po-irreflexive refl)
... | tri> ¬po[xy]ᵗ x≢y   po[yx]ᵗ =
  case ×-dec (ev-eq-dec x ev₃) (ev-eq-dec y ev₁) of
  λ{ (yes (refl , refl)) → tri< po₃₁ˢ (ev₁≢ev₃ ∘ with-pred-≡ ∘ ≡-sym) ¬po₁₃ˢ
   ; (no ¬31) →
       case ×-dec (ev-eq-dec x ev₂) (ev-eq-dec y ev₁) of
       λ{ (yes (refl , refl)) → tri< po₂₁ˢ (ev₁≢ev₂ ∘ with-pred-≡ ∘ ≡-sym) ¬po₁₂ˢ
        ; (no ¬21) → tri> (¬po[⇐] ¬21 ¬31 ¬po[xy]ᵗ) (λ{refl → ¬po[xy]ᵗ po[yx]ᵗ}) (po[⇐] (¬21 ∘ swap) (¬31 ∘ swap) po[yx]ᵗ)
        }
   }



src-po-splittable : SplittableOrder (po src)
src-po-splittable = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : po src ⊆₂' TransClosure (po-imm src)
  ⊆-proof x y po[xy]ˢ with ×-dec (ev-eq-dec x ev₂) (ev-eq-dec y ev₁)
  ... | yes (refl , refl) = pi₂₃ˢ ∷ [ pi₃₁ˢ ]
  ... | no ¬21 with ×-dec (ev-eq-dec x ev₃) (ev-eq-dec y ev₁)
  ... | yes (refl , refl) = [ pi₃₁ˢ ]
  ... | no ¬31 =
    let po[xy]ᵗ = po[⇒] ¬21 ¬31 po[xy]ˢ
        pi⁺[xy]ᵗ = ⇔₂-apply-⊆₂ (po-splittable dst-wf) po[xy]ᵗ
    in pi⁺[⇐] (λ{(refl , refl) → ¬po₁₂ˢ po[xy]ˢ}) (λ{(refl , refl) → ¬po₁₃ˢ po[xy]ˢ}) pi⁺[xy]ᵗ

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
  lemma x y (po-new₂₁ refl refl) =
    case ⊆₂-apply (po-stid dst-wf) po₁₂ᵗ of
    λ{ (inj₁ (ev-init , _)) → ⊥-elim (¬init₁ ev-init)
     ; (inj₂ yx-stid) → inj₂ (sym-same-tid yx-stid)
     }
  lemma x y (po-new₃₁ refl refl) =
    case ⊆₂-apply (po-stid dst-wf) po₁₃ᵗ of
    λ{ (inj₁ (ev-init , _)) → ⊥-elim (¬init₁ ev-init)
     ; (inj₂ yx-stid) → inj₂ (sym-same-tid yx-stid)
     }
  lemma x y (po-dst _ _ po[xy]) = ⊆₂-apply (po-stid dst-wf) po[xy]


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
