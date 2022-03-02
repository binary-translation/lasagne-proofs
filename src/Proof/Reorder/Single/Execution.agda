{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder using (ReorderRestricted)


module Proof.Reorder.Single.Execution
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; _∘₂_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂; swap; <_,_>)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Transitive; Irreflexive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _++_)
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
-- Local imports: Theorem Specification
open import TransformReorder


open Execution
open WellFormed
open ReorderRestricted dst-res
open TransformReorder.Extra dst-res


--
-- File Structure:
-- + Definitions
-- + Mapping
-- ++ po
-- ++ po⁺
-- ++ ¬po
-- ++ pi
-- ++ pi⁺
-- ++ po udr
-- ++ ghb
--


dst-ok : IsLIMMConsistent dst
dst-ok = consistent

dst-wf : WellFormed dst
dst-wf = wellformed


-- # Definitions

-- |
--
-- Note that 2-1 is the /order in the source/.
-- While 1-2 is the /order in the target/.
data SrcPo (x y : Event LabelLIMM) : Set where
  -- | Any po-order from the source, except the cut 1-2 pair
  po-dst : ¬ (x ≡ ev₁ × y ≡ ev₂) → po dst x y → SrcPo x y
  -- | The new 2-1 pair
  po-new : x ≡ ev₂ → y ≡ ev₁ → SrcPo x y


src : Execution LabelLIMM
src =
  record
    { events = events dst
    ; po     = SrcPo
    ; rf     = rf dst
    ; co     = co dst
    ; rmw    = rmw dst
    }


-- # Helpers

ev₁≢ev₂ : ev₁ ≢ ev₂
ev₁≢ev₂ 1≡2 = po-irreflexive dst-wf 1≡2 po[12]ᵗ

src-po-trans : Transitive (po src)
src-po-trans {x} {y} {z} (po-dst ¬[1x2y] po[xy]) (po-dst ¬[1y2z] po[yz]) =
  let ¬[1x2z] : ¬ (x ≡ ev₁ × z ≡ ev₂)
      ¬[1x2z] = λ{(refl , refl) → proj₂ pi[12]ᵗ (_ , po[xy] , [ po[yz] ])}
  in po-dst ¬[1x2z] (po-trans dst-wf po[xy] po[yz])
src-po-trans {x} (po-dst ¬[1x2y] po[x2]ᵗ) (po-new y≡2@refl z≡1@refl) =
  let x≢1 = λ{x≡1 → ¬[1x2y] (x≡1 , y≡2)}
      po[x1]ᵗ = ⊥⊎-elim x≢1 id (unsplit-poʳ dst-wf po[x2]ᵗ pi[12]ᵗ)
      ¬[1x21] = λ{(x≡1 , 1≡2) → ⊥-elim (x≢1 x≡1)}
  in po-dst ¬[1x21] po[x1]ᵗ
src-po-trans {x} {y} {z} (po-new x≡2@refl y≡1@refl) (po-dst ¬[1y2z] po[yz]) =
  let 2≢z = λ{2≡z → ¬[1y2z] (y≡1 , ≡-sym 2≡z)}
      po[2z]ᵗ = ⊥⊎-elim 2≢z id (unsplit-poˡ dst-wf ¬init₁ po[yz] pi[12]ᵗ)
      ¬[122z] = λ{(2≡1 , z≡2) → ⊥-elim (2≢z (≡-sym z≡2))}
  in po-dst ¬[122z] po[2z]ᵗ
src-po-trans (po-new refl refl) (po-new refl refl) = ⊥-elim (ev₁≢ev₂ refl)

src-po-irreflexive : Irreflexive _≡_ (po src)
src-po-irreflexive refl (po-new refl refl) = po-irreflexive dst-wf refl po[12]ᵗ
src-po-irreflexive refl (po-dst _ po[xx])  = po-irreflexive dst-wf refl po[xx]

src-po-acyclic : Acyclic _≡_ (po src)
src-po-acyclic refl po⁺[xx] = 
  let po[xx] = ⊆₂-apply (⁺-trans-⊆₂ src-po-trans) po⁺[xx]
  in src-po-irreflexive refl po[xx]

poʳ∈src : ∀ {x y : Event LabelLIMM} → po src x y → y ∈ events src
poʳ∈src (po-dst _ po[xy])  = poʳ∈ex dst-wf po[xy]
poʳ∈src (po-new refl refl) = ev₁∈ex


-- # Mapping

-- ## Mapping: po

po[⇒] : {x y : Event LabelLIMM} → ¬ (x ≡ ev₂ × y ≡ ev₁) → po src x y → po dst x y
po[⇒] ¬xy (po-dst ¬[1x2y] po[xy]ᵗ) = po[xy]ᵗ
po[⇒] ¬xy (po-new x≡2 y≡1)         = ⊥-elim (¬xy (x≡2 , y≡1))

po[⇒]ˡ : {x y : Event LabelLIMM} → x ≢ ev₂ → po src x y → po dst x y
po[⇒]ˡ = po[⇒] ∘ (_∘ proj₁)

po[⇒]ʳ : {x y : Event LabelLIMM} → y ≢ ev₁ → po src x y → po dst x y
po[⇒]ʳ = po[⇒] ∘ (_∘ proj₂)

poˡ-1[⇒]2 : {y : Event LabelLIMM} → po src ev₁ y → po dst ev₂ y
poˡ-1[⇒]2 (po-dst ¬[112y] po[1y]ᵗ) =
  let y≢2 = λ{y≡2 → ¬[112y] (refl , y≡2)}
  in ⊥⊎-elim (≢-sym y≢2) id (unsplit-poˡ dst-wf ¬init₁ po[1y]ᵗ pi[12]ᵗ)
poˡ-1[⇒]2 (po-new refl refl) = ⊥-elim (ev₁≢ev₂ refl)

poʳ-2[⇒]1 : {x : Event LabelLIMM} → po src x ev₂ → po dst x ev₁
poʳ-2[⇒]1 (po-dst ¬[1x22] po[x2]ᵗ) =
  let x≢1 = λ{x≡1 → ¬[1x22] (x≡1 , refl)}
  in ⊥⊎-elim x≢1 id (unsplit-poʳ dst-wf po[x2]ᵗ pi[12]ᵗ)
poʳ-2[⇒]1 (po-new refl refl) = ⊥-elim (ev₁≢ev₂ refl)

po[⇐] : {x y : Event LabelLIMM} → ¬ (x ≡ ev₁ × y ≡ ev₂) → po dst x y → po src x y
po[⇐] = po-dst

po[⇐]ˡ : {x y : Event LabelLIMM} → x ≢ ev₁ → po dst x y → po src x y
po[⇐]ˡ = po[⇐] ∘ (_∘ proj₁)

po[⇐]ʳ : {x y : Event LabelLIMM} → y ≢ ev₂ → po dst x y → po src x y
po[⇐]ʳ = po[⇐] ∘ (_∘ proj₂)

poʳ-1[⇐]2 : {x : Event LabelLIMM} → po dst x ev₁ → po src x ev₂
poʳ-1[⇐]2 po[x1] =
  let x≢ev₁ = λ{refl → po-irreflexive dst-wf refl po[x1]}
  in po[⇐]ˡ x≢ev₁ (po-trans dst-wf po[x1] po[12]ᵗ)

poˡ-2[⇐]1 : {y : Event LabelLIMM} → po dst ev₂ y → po src ev₁ y
poˡ-2[⇐]1 po[2y] =
  let y≢ev₂ = λ{refl → po-irreflexive dst-wf refl po[2y]}
  in po[⇐]ʳ y≢ev₂ (po-trans dst-wf po[12]ᵗ po[2y])


-- ### Mapping - po: Forward

po⁺[⇒] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₂ × y ≡ ev₁)
  → TransClosure (po src) x y
    -------------------------
  → TransClosure (po dst) x y
po⁺[⇒] ¬xy po⁺[xy] =
  let po[xy] = ⊆₂-apply (⁺-trans-⊆₂ src-po-trans) po⁺[xy]
  in [ po[⇒] ¬xy po[xy] ]


-- ## Mapping: ¬po

¬po[⇐]ˡ : {x y : Event LabelLIMM} → x ≢ ev₂ → ¬ po dst x y → ¬ po src x y
¬po[⇐]ˡ = contrapositive ∘ po[⇒]ˡ

¬po[⇐]ʳ : {x y : Event LabelLIMM} → y ≢ ev₁ → ¬ po dst x y → ¬ po src x y
¬po[⇐]ʳ = contrapositive ∘ po[⇒]ʳ

¬po[⇒] : {x y : Event LabelLIMM} → ¬ (x ≡ ev₁ × y ≡ ev₂) → ¬ po src x y → ¬ po dst x y
¬po[⇒] ¬xy ¬po[xy]ˢ po[xy]ᵗ = ¬po[xy]ˢ (po-dst ¬xy po[xy]ᵗ)


-- ## Mapping: pi

-- These are numerous. There are several (main) cases to consider:
-- * po-imm src 2 y ⇒ y ≡ 1
-- * po-imm src x 1 ⇒ x ≡ 2
-- * po-imm dst 1 y ⇒ y ≡ 2
-- * po-imm dst x 2 ⇒ x ≡ 1
-- * po-imm src 1 y ↔ po-imm dst 2 y
-- * po-imm src x 2 ↔ po-imm dst x 1
-- * po-imm src x y ↔ po-imm dst x y ; otherwise


pi[21]ˢ : po-imm src ev₂ ev₁
pi[21]ˢ = po-new refl refl , ¬∃z'
  where
  ¬∃z' : ¬ (∃[ z ] (po src ev₂ z × TransClosure (po src) z ev₁))
  ¬∃z' (z , po[2z] , po⁺[z1]) = 
    let po[z1] = ⁺-join-trans src-po-trans po⁺[z1]
        z≢ev₁ = λ{refl → src-po-acyclic refl po⁺[z1]}
        z≢ev₂ = λ{refl → src-po-irreflexive refl po[2z]}
        dst-po[z1] = po[⇒]ˡ z≢ev₂ po[z1]
        dst-po[z2] = po-trans dst-wf dst-po[z1] po[12]ᵗ
        dst-po[2z] = po[⇒]ʳ z≢ev₁ po[2z]
    in po-irreflexive dst-wf refl (po-trans dst-wf dst-po[z2] dst-po[2z])

piʳ-1[⇐]2 : {x : Event LabelLIMM} → po-imm dst x ev₁ → po-imm src x ev₂
piʳ-1[⇐]2 {x} (po[x1] , ¬∃z) = poʳ-1[⇐]2 po[x1] , ¬∃z'
  where
  ¬∃z' : ¬ (∃[ z ] (po src x z × TransClosure (po src) z ev₂))
  ¬∃z' (z , po[xz] , po⁺[z2]) =
    let po[z2] = ⁺-join-trans src-po-trans po⁺[z2]
        po[x2] = src-po-trans po[xz] po[z2]
        x≢ev₂ = λ{refl → src-po-irreflexive refl po[x2]}
    in ¬∃z (z , po[⇒]ˡ x≢ev₂ po[xz] , [ poʳ-2[⇒]1 po[z2] ])


piˡ-2[⇐]1 : {y : Event LabelLIMM} → po-imm dst ev₂ y → po-imm src ev₁ y
piˡ-2[⇐]1 {y} (po[2y] , ¬∃z) = poˡ-2[⇐]1 po[2y] , ¬∃z'
  where
  ¬∃z' : ¬ (∃[ z ] (po src ev₁ z × TransClosure (po src) z y))
  ¬∃z' (z , po[1z] , po⁺[zy]) =
    let po[zy] = ⁺-join-trans src-po-trans po⁺[zy]
        po[1y] = src-po-trans po[1z] po[zy]
        y≢ev₁ = λ{refl → src-po-irreflexive refl po[1y]}
    in ¬∃z (z , poˡ-1[⇒]2 po[1z] , [ po[⇒]ʳ y≢ev₁ po[zy] ])


pi[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₂)
  → y ≢ ev₁
  → x ≢ ev₂
  → po-imm dst x y
  → po-imm src x y
pi[⇐] {x} {y} ¬xy y≢ev₁ x≢ev₂ (po[xy] , ¬∃z) = po[⇐] ¬xy po[xy] , ¬∃z'
  where
  ¬∃z' : ¬ (∃[ z ] (po src x z × TransClosure (po src) z y))
  ¬∃z' (z , po[xz]ˢ , po⁺[zy]ˢ) =
    let po[xz]ᵗ  = po[⇒] (x≢ev₂ ∘ proj₁) po[xz]ˢ
        po⁺[zy]ᵗ = po⁺[⇒] (y≢ev₁ ∘ proj₂) po⁺[zy]ˢ
    in ¬∃z (z , po[xz]ᵗ , po⁺[zy]ᵗ)


-- ## Mapping: pi⁺

pi⁺ˡ-2[⇐]1 : {y : Event LabelLIMM}
  → TransClosure (po-imm dst) ev₂ y
    -------------------------------
  → TransClosure (po-imm src) ev₁ y
pi⁺ˡ-2[⇐]1 [ pi[2y] ] = [ piˡ-2[⇐]1 pi[2y] ]
pi⁺ˡ-2[⇐]1 ( pi[2x] ∷ pi⁺[xy] ) =
  piˡ-2[⇐]1 pi[2x] ∷ lemma (proj₁ pi[2x]) pi⁺[xy]
  where
  pi[⇐]acc : {x y : Event LabelLIMM} → po dst ev₂ x → po-imm dst x y → po-imm src x y
  pi[⇐]acc po[2x] pi[xy] =
    let po[2y] = po-trans dst-wf po[2x] (proj₁ pi[xy])
        po[1y] = po-trans dst-wf po[12]ᵗ po[2y]
        x≢2 = λ{x≡2 → po-irreflexive dst-wf (≡-sym x≡2) po[2x]}
        y≢1 = λ{y≡1 → po-irreflexive dst-wf (≡-sym y≡1) po[1y]}
        y≢2 = λ{y≡2 → po-irreflexive dst-wf (≡-sym y≡2) po[2y]}
    in pi[⇐] (y≢2 ∘ proj₂) y≢1 x≢2 pi[xy]
  
  lemma : {x y : Event LabelLIMM}
    → po dst ev₂ x
    → TransClosure (po-imm dst) x y
    → TransClosure (po-imm src) x y
  lemma po[2x] [ pi[xy] ] = [ pi[⇐]acc po[2x] pi[xy] ]
  lemma po[2x] ( pi[xz] ∷ pi⁺[zy] ) =
    pi[⇐]acc po[2x] pi[xz] ∷ lemma (po-trans dst-wf po[2x] (proj₁ pi[xz])) pi⁺[zy]


pi⁺ʳ-1[⇐]2 : {x : Event LabelLIMM}
  → TransClosure (po-imm dst) x ev₁
    -------------------------------
  → TransClosure (po-imm src) x ev₂
pi⁺ʳ-1[⇐]2 [ pi[x1] ] = [ piʳ-1[⇐]2 pi[x1] ]
pi⁺ʳ-1[⇐]2 ( pi[xy] ∷ pi⁺[y1] ) =
  let po[y1] = po⁺⇒po dst-wf (⁺-map _ proj₁ pi⁺[y1])
      po[y2] = po-trans dst-wf po[y1] po[12]ᵗ
      po[x2] = po-trans dst-wf (proj₁ pi[xy]) po[y2]
      y≢1 = λ{y≡1 → po-irreflexive dst-wf y≡1 po[y1]}
      y≢2 = λ{y≡2 → po-irreflexive dst-wf y≡2 po[y2]}
      x≢2 = λ{x≡2 → po-irreflexive dst-wf x≡2 po[x2]}
  in pi[⇐] (y≢2 ∘ proj₂) y≢1 x≢2 pi[xy] ∷ pi⁺ʳ-1[⇐]2 pi⁺[y1]


-- |
-- Note that `po-imm` is not generally preserved to the re-ordered events,
-- but often there exists a po-imm chain anyway.
pi[⇐]pi⁺ : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₂)
  → po-imm dst x y
  → TransClosure (po-imm src) x y
pi[⇐]pi⁺ {x} {y} ¬xy pi[xy] with ev-eq-dec x ev₂ | ev-eq-dec y ev₁
... | yes refl | _        = pi[21]ˢ ∷ [ piˡ-2[⇐]1 pi[xy] ] -- pi[2y] → pi[21] pi[1y]
... | no x≢2   | yes refl = piʳ-1[⇐]2 pi[xy] ∷ [ pi[21]ˢ ] -- pi[x1] → pi[x2] pi[21]
... | no x≢2   | no y≢1   = [ pi[⇐] ¬xy y≢1 x≢2 pi[xy] ]


pi⁺[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₂)
  → TransClosure (po-imm dst) x y
  → TransClosure (po-imm src) x y
pi⁺[⇐] {x} {y} ¬xy [ pi[xy]ᵗ ] = pi[⇐]pi⁺ ¬xy pi[xy]ᵗ
pi⁺[⇐] {x} {y} ¬xy ( _∷_ {x} {z} pi[xz]ᵗ pi⁺[zy]ᵗ )
  with ev-eq-dec z ev₂
... | yes refl =
  let x≡1 = po-immˡ dst-wf pi[xz]ᵗ pi[12]ᵗ
  in subst-rel (TransClosure (po-imm src)) (≡-sym x≡1) refl (pi⁺ˡ-2[⇐]1 pi⁺[zy]ᵗ)
... | no z≢2 with ×-dec (ev-eq-dec z ev₁) (ev-eq-dec y ev₂)
... | yes (refl , refl) = pi⁺ʳ-1[⇐]2 [ pi[xz]ᵗ ]
... | no ¬zy = pi[⇐]pi⁺ (z≢2 ∘ proj₂) pi[xz]ᵗ ++ pi⁺[⇐] ¬zy pi⁺[zy]ᵗ


-- ## Mapping: po udr

udr-po[⇒] : {x : Event LabelLIMM} → x ∈ udr (po src) → x ∈ udr (po dst)
udr-po[⇒] {x} (inj₁ (y , po-new refl refl)) = ev₂∈po
udr-po[⇒] {x} (inj₁ (y , po-dst _ po[xy]))  = take-udrˡ (po dst) po[xy]
udr-po[⇒] {y} (inj₂ (x , po-new refl refl)) = ev₁∈po
udr-po[⇒] {y} (inj₂ (x , po-dst _ po[xy]))  = take-udrʳ (po dst) po[xy]

udr-po[⇐] : {x : Event LabelLIMM} → x ∈ udr (po dst) → x ∈ udr (po src)
udr-po[⇐] {x} (inj₁ (y , po[yx])) with ×-dec (ev-eq-dec x ev₁) (ev-eq-dec y ev₂)
... | yes (refl , refl) = take-udrʳ (po src) (po-new refl refl)
... | no ¬xy            = take-udrˡ (po src) (po-dst ¬xy po[yx])
udr-po[⇐] {x} (inj₂ (y , po[xy]))  with ×-dec (ev-eq-dec y ev₁) (ev-eq-dec x ev₂)
... | yes (refl , refl) = take-udrˡ (po src) (po-new refl refl)
... | no ¬xy            = take-udrʳ (po src) (po-dst ¬xy po[xy])

-- ## Mapping: ghb

private
  -- A (weirdly) specific split. Used to handle the `pord-scˡ` case.
  rw-split-r-rmw : ∀ {x : Event LabelLIMM} → EvRW x → (EvRₜ trmw ∪₁ (EvRₜ tmov ∪₁ EvW)) x
  rw-split-r-rmw {event-init _ _ _}           ev-init     = inj₂ (inj₂ ev-init)
  rw-split-r-rmw {event _ _ (lab-r tmov _ _)} (ev-r is-r) = inj₂ (inj₁ (ev-r is-r refl))
  rw-split-r-rmw {event _ _ (lab-w tmov _ _)} (ev-w is-w) = inj₂ (inj₂ (ev-w is-w))
  rw-split-r-rmw {event _ _ (lab-r trmw _ _)} (ev-r is-r) = inj₁ (ev-r is-r refl)
  rw-split-r-rmw {event _ _ (lab-w trmw _ _)} (ev-w is-w) = inj₂ (inj₂ (ev-w is-w))

  --
  -- Example:
  -- > po[⇒]rule pord-rmˡ x-rᵣ y-rm po[xy]
  --
  -- This is a helper that produces mapping functions from any rule in
  -- `ReorderRestricted`.
  po[⇒]rule :
    ∀ {P₁ P₂ : Pred (Event LabelLIMM) ℓzero}
    → ¬ (P₁ ev₂ × P₂ ev₁) -- The rule from `ReorderRestricted`
      -----------------------
    → {x y : Event LabelLIMM}
    → P₁ x
    → P₂ y
    → po src x y
      ----------
    → po dst x y
  po[⇒]rule f x-p₁ y-p₂ = po[⇒] (λ{(x≡2 , y≡1) → f (subst _ x≡2 x-p₁ , subst _ y≡1 y-p₂)})
  

ord[⇒] : {x y : Event LabelLIMM} → OrdAlt src x y → OrdAlt dst x y
ord[⇒] {x} {y} (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
  let x≢2 = λ{x≡2 → ¬init₂ (subst EvInit x≡2 x-init)}
  in ord-init ((refl , x-init) ⨾[ _ ]⨾ po[⇒]ˡ x≢2 po[xy] ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz]ˢ ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zy]ˢ ⨾[ _ ]⨾ (refl , y-rw)))
  with r/tag x-r
... | inj₁ x-rᵣ =
  let po[xz]ᵗ = po[⇒]rule pord-rmˡ x-rᵣ z-rm po[xz]ˢ
      po[zy]ᵗ = po[⇒]rule pord-rmʳ z-rm y-rw po[zy]ˢ
  in ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))
... | inj₂ x-rₐ =
  let po[xy]ˢ = src-po-trans po[xz]ˢ po[zy]ˢ
      po[xy]ᵗ = po[⇒]rule pord-rmw-rʳ x-rₐ y-rw po[xy]ˢ
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] (ord-ww ((refl , x-w) ⨾[ x ]⨾ po[xz]ˢ ⨾[ z ]⨾ (refl , z-ww) ⨾[ _ ]⨾ po[zy]ˢ ⨾[ y ]⨾ (refl , y-w))) =
  let po[xz]ᵗ = po[⇒]rule pord-wwˡ x-w z-ww po[xz]ˢ
      po[zy]ᵗ = po[⇒]rule pord-wwʳ z-ww y-w po[zy]ˢ
  in ord-ww ((refl , x-w) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , z-ww) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , y-w))
ord[⇒] (ord-sc ((refl , x-rw) ⨾[ x ]⨾ po[xz]ˢ ⨾[ z ]⨾ (refl , z-sc) ⨾[ z ]⨾ po[zy]ˢ ⨾[ y ]⨾ (refl , y-rw)))
  with rw-split-r-rmw x-rw
... | inj₁ x-rₐ   =
  let po[xy]ˢ = src-po-trans po[xz]ˢ po[zy]ˢ
      po[xy]ᵗ = po[⇒]rule pord-rmw-rʳ x-rₐ y-rw po[xy]ˢ
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))
... | inj₂ x-rᵣ/w =
  let po[xz]ᵗ = po[⇒]rule pord-scˡ x-rᵣ/w z-sc po[xz]ˢ
      po[zy]ᵗ = po[⇒]rule pord-scʳ z-sc y-rw po[zy]ˢ
  in ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] (ord-rmw-dom ((refl , x-rw) ⨾[ x ]⨾ po[xy]ˢ ⨾[ y ]⨾ (refl , y∈rmwˡ))) =
  let y-rₐ = rmwˡ-r dst-wf y∈rmwˡ
      po[xy]ᵗ = po[⇒]ʳ (λ{y≡1 → ¬rmw₁ (subst (udr (rmw dst)) y≡1 (inj₁ y∈rmwˡ))}) po[xy]ˢ
  in ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y∈rmwˡ))
ord[⇒] (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy]ˢ ⨾[ _ ]⨾ (refl , y-rw))) =
  let po[xy]ᵗ = po[⇒]ˡ (λ{x≡2 → ¬rmw₂ (subst (udr (rmw dst)) x≡2 (inj₂ x∈rmwʳ))}) po[xy]ˢ
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] (ord-w ((refl , x-rw) ⨾[ x ]⨾ po[xy]ˢ ⨾[ y ]⨾ (refl , y-wₐ))) =
  let y∈ex = poʳ∈src po[xy]ˢ
      y∈rmwʳ = ⇔₁-apply-⊇₁ (rmw-w dst-wf) (y∈ex , y-wₐ)
      po[xy]ᵗ = po[⇒]ʳ (λ{y≡1 → ¬rmw₁ (subst (udr (rmw dst)) y≡1 (inj₂ y∈rmwʳ))}) po[xy]ˢ
  in ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-wₐ))
ord[⇒] (ord-r ((refl , x-rₐ) ⨾[ x ]⨾ po[xy]ˢ ⨾[ y ]⨾ (refl , y-rw))) =
  let po[xy]ᵗ = po[⇒]rule pord-rmw-rʳ x-rₐ y-rw po[xy]ˢ
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))


rfe[⇒] : {x y : Event LabelLIMM} → rfe src x y → rfe dst x y
rfe[⇒] (rf[xy] , ¬po[xy]) =
  let xy-sloc = ⊆₂-apply (rf-sloc dst-wf) rf[xy]
  in rf[xy] , ¬po[⇒] (λ{(x≡1 , y≡2) → ¬same-loc (subst-rel SameLoc x≡1 y≡2 xy-sloc)}) ¬po[xy]

coe[⇒] : {x y : Event LabelLIMM} → coe src x y → coe dst x y
coe[⇒] (co[xy] , ¬po[xy]) =
  let xy-sloc = ⊆₂-apply (co-sloc dst-wf) co[xy]
  in co[xy] , ¬po[⇒] (λ{(x≡1 , y≡2) → ¬same-loc (subst-rel SameLoc x≡1 y≡2 xy-sloc)}) ¬po[xy]

fre[⇒] : {x y : Event LabelLIMM} → fre src x y → fre dst x y
fre[⇒] (fr[xy] , ¬po[xy]) =
  let xy-sloc = ⊆₂-apply (fr-sloc dst-wf) fr[xy]
  in fr[xy] , ¬po[⇒] (λ{(x≡1 , y≡2) → ¬same-loc (subst-rel SameLoc x≡1 y≡2 xy-sloc)}) ¬po[xy]

ghbi[⇒] : {x y : Event LabelLIMM} → GhbiAlt src x y → GhbiAlt dst x y
ghbi[⇒] (ghbi-ord ord[xy]) = ghbi-ord (ord[⇒] ord[xy])
ghbi[⇒] (ghbi-rfe rfe[xy]) = ghbi-rfe (rfe[⇒] rfe[xy])
ghbi[⇒] (ghbi-coe coe[xy]) = ghbi-coe (coe[⇒] coe[xy])
ghbi[⇒] (ghbi-fre fre[xy]) = ghbi-fre (fre[⇒] fre[xy])
