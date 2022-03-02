{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder21 using (ReorderRestricted21)


-- |
--
module Proof.Reorder.Reorder21.Execution
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted21 dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂; swap)
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


open Execution
open IsLIMMConsistent
open WellFormed
open ReorderRestricted21 dst-res
open TransformReorder21.Extra dst-res


--
-- Most of this modules consists of the many lemmas & sub-proofs for `pi⁺[⇐]`.
--


dst-ok : IsLIMMConsistent dst
dst-ok = consistent

dst-wf : WellFormed dst
dst-wf = wellformed


-- # Definitions

data SrcPo (x y : Event LabelLIMM) : Set where
  po-dst : ¬ (x ≡ ev₁ × y ≡ ev₂) → ¬ (x ≡ ev₁ × y ≡ ev₃) → po dst x y → SrcPo x y
  po-new₂₁ : x ≡ ev₂ → y ≡ ev₁ → SrcPo x y
  po-new₃₁ : x ≡ ev₃ → y ≡ ev₁ → SrcPo x y

src : Execution LabelLIMM
src =
  record
    { events = events dst
    ; po = SrcPo
    ; rf = rf dst
    ; co = co dst
    ; rmw = rmw dst
    }


-- # Helpers

src-po-irreflexive : Irreflexive _≡_ SrcPo
src-po-irreflexive refl (po-new₂₁ refl refl) = ⊥-elim (ev₁≢ev₂ refl)
src-po-irreflexive refl (po-new₃₁ refl refl) = ⊥-elim (ev₁≢ev₃ refl)
src-po-irreflexive refl (po-dst _ _ po[xy]) = po-irreflexive dst-wf refl po[xy]

src-po-trans : Transitive SrcPo
src-po-trans (po-new₂₁ refl refl) (po-dst ¬12 _ po[1z]) -- goal: po src ev₂ z
  with unsplit-poˡ dst-wf ¬init₁ po[1z] pi₁₂ᵗ
... | inj₁ refl   = ⊥-elim (¬12 (refl , refl)) -- z ≡ 2
... | inj₂ po[2z] = po-dst (≢-sym ev₁≢ev₂ ∘ proj₁) (≢-sym ev₁≢ev₂ ∘ proj₁) po[2z]
src-po-trans (po-new₃₁ refl refl) (po-dst ¬12 ¬13 po[1z]) -- goal: po src ev₃ z
  with unsplit-poˡ dst-wf ¬init₁ po[1z] pi₁₂ᵗ
... | inj₁ refl   = ⊥-elim (¬12 (refl , refl)) -- z ≡ 2
... | inj₂ po[2z]
  with unsplit-poˡ dst-wf ¬init₂ po[2z] pi₂₃ᵗ
... | inj₁ refl   = ⊥-elim (¬13 (refl , refl)) -- z ≡ 3
... | inj₂ po[3z] = po-dst (≢-sym ev₁≢ev₃ ∘ proj₁) (≢-sym ev₁≢ev₃ ∘ proj₁) po[3z]
src-po-trans (po-dst ¬12 ¬23 po[x2]) (po-new₂₁ refl refl) -- goal: po src x ev₁
  with unsplit-poʳ dst-wf po[x2] pi₁₂ᵗ
... | inj₁ refl   = ⊥-elim (¬12 (refl , refl))
... | inj₂ po[x1] = po-dst (ev₁≢ev₂ ∘ proj₂) (ev₁≢ev₃ ∘ proj₂) po[x1]
src-po-trans (po-dst ¬12 ¬13 po[x3]) (po-new₃₁ refl refl) -- goal: po src x ev₁
  with unsplit-poʳ dst-wf po[x3] pi₂₃ᵗ
... | inj₁ refl   = po-new₂₁ refl refl -- x ≡ 2
... | inj₂ po[x2]
  with unsplit-poʳ dst-wf po[x2] pi₁₂ᵗ
... | inj₁ refl = ⊥-elim (¬13 (refl , refl)) -- x ≡ 1
... | inj₂ po[x1] = po-dst (ev₁≢ev₂ ∘ proj₂) (ev₁≢ev₃ ∘ proj₂) po[x1]
src-po-trans {_} {y} (po-dst ¬12ˡ ¬13ˡ po[xy]) (po-dst ¬12ʳ ¬13ʳ po[yz]) =
  po-dst
    (λ{(refl , refl) → proj₂ pi₁₂ᵗ (_ , po[xy] , [ po[yz] ])})
    (λ{(refl , refl) → ¬12ˡ (refl , lemma po[xy] po[yz])})
    (po-trans dst-wf po[xy] po[yz])
  where
  lemma : po dst ev₁ y → po dst y ev₃ → y ≡ ev₂
  lemma po[1y] po[y3] with unsplit-poʳ dst-wf po[y3] pi₂₃ᵗ
  ... | inj₁ refl   = refl -- y ≡ 2
  ... | inj₂ po[y2] = ⊥-elim (proj₂ pi₁₂ᵗ (_ , po[1y] , [ po[y2] ]))
-- Impossible cases
src-po-trans (po-new₂₁ refl refl) (po-new₂₁ refl refl) = ⊥-elim (ev₁≢ev₂ refl)
src-po-trans (po-new₂₁ refl refl) (po-new₃₁ refl refl) = ⊥-elim (ev₁≢ev₃ refl)
src-po-trans (po-new₃₁ refl refl) (po-new₂₁ refl refl) = ⊥-elim (ev₁≢ev₂ refl)
src-po-trans (po-new₃₁ refl refl) (po-new₃₁ refl refl) = ⊥-elim (ev₁≢ev₃ refl)

poˡ∈src : {x y : Event LabelLIMM} → po src x y → x ∈ events src
poˡ∈src (po-new₂₁ refl _)   = ev₂∈ex
poˡ∈src (po-new₃₁ refl _)   = ev₃∈ex
poˡ∈src (po-dst _ _ po[xy]) = poˡ∈ex dst-wf po[xy]

poʳ∈src : {x y : Event LabelLIMM} → po src x y → y ∈ events src
poʳ∈src (po-new₂₁ _ refl)   = ev₁∈ex
poʳ∈src (po-new₃₁ _ refl)   = ev₁∈ex
poʳ∈src (po-dst _ _ po[xy]) = poʳ∈ex dst-wf po[xy]


-- # Mapping

-- ## Mapping: po

po[⇒] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₂ × y ≡ ev₁)
  → ¬ (x ≡ ev₃ × y ≡ ev₁)
  → po src x y
    -------------------------------------------
  → po dst x y
po[⇒] ¬21 ¬31 (po-new₂₁ refl refl) = ⊥-elim (¬21 (refl , refl))
po[⇒] ¬21 ¬31 (po-new₃₁ refl refl) = ⊥-elim (¬31 (refl , refl))
po[⇒] ¬21 ¬31 (po-dst _ _ po[xy]) = po[xy]

po[⇒]ˡ : {x y : Event LabelLIMM}
  → x ≢ ev₂
  → x ≢ ev₃
  → po src x y
    ----------
  → po dst x y
po[⇒]ˡ x≢ev₂ x≢ev₃ = po[⇒] (x≢ev₂ ∘ proj₁) (x≢ev₃ ∘ proj₁)

po[⇒]ʳ : {x y : Event LabelLIMM}
  → y ≢ ev₁
  → po src x y
    ----------
  → po dst x y
po[⇒]ʳ y≢ev₁ = po[⇒] (y≢ev₁ ∘ proj₂) (y≢ev₁ ∘ proj₂)


po[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₂)
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → po dst x y
    -------------------------------------------
  → po src x y
po[⇐] = po-dst

po[⇐]ˡ : {x y : Event LabelLIMM}
  → x ≢ ev₁
  → po dst x y
    ----------
  → po src x y
po[⇐]ˡ x≢1 = po[⇐] (x≢1 ∘ proj₁) (x≢1 ∘ proj₁)

po[⇐]ʳ : {x y : Event LabelLIMM}
  → y ≢ ev₂
  → y ≢ ev₃
  → po dst x y
    -------------------------------------------
  → po src x y
po[⇐]ʳ y≢2 y≢3 = po[⇐] (y≢2 ∘ proj₂) (y≢3 ∘ proj₂)

po₃₁ˢ : po src ev₃ ev₁
po₃₁ˢ = po-new₃₁ refl refl

po₂₃ˢ : po src ev₂ ev₃
po₂₃ˢ = po-dst (≢-sym ev₁≢ev₂ ∘ proj₁) (≢-sym ev₁≢ev₂ ∘ proj₁) po₂₃ᵗ

pi₂₃ˢ : po-imm src ev₂ ev₃
pi₂₃ˢ = po₂₃ˢ , ¬∃z
  where
  ¬∃z : ¬ (∃[ z ] (po src ev₂ z × TransClosure (po src) z ev₃))
  ¬∃z (z , po[2z]ˢ , po⁺[z3]ˢ) =
    let po[z3]ˢ = ⁺-join-trans src-po-trans po⁺[z3]ˢ
        po[z1]ˢ = src-po-trans po[z3]ˢ po₃₁ˢ
        z≢1 = λ{z≡1 → src-po-irreflexive z≡1 po[z1]ˢ}
        z≢2 = λ{z≡2 → src-po-irreflexive (≡-sym z≡2) po[2z]ˢ}
        z≢3 = λ{z≡3 → src-po-irreflexive z≡3 po[z3]ˢ}
        po[2z]ᵗ = po[⇒]ʳ z≢1 po[2z]ˢ
        po[z3]ᵗ = po[⇒]ˡ z≢2 z≢3 po[z3]ˢ
    in proj₂ pi₂₃ᵗ (z , po[2z]ᵗ , [ po[z3]ᵗ ])

pi₃₁ˢ : po-imm src ev₃ ev₁
pi₃₁ˢ = po₃₁ˢ , ¬∃z
  where
  ¬∃z : ¬ (∃[ z ] (po src ev₃ z × TransClosure (po src) z ev₁))
  ¬∃z (z , po[3z]ˢ , po⁺[z1]ˢ) =
    let po[z1]ˢ = ⁺-join-trans src-po-trans po⁺[z1]ˢ
        z≢1 = λ{z≡1 → src-po-irreflexive z≡1 po[z1]ˢ}
        z≢2 = λ{z≡2 → src-po-irreflexive (≡-sym z≡2) (src-po-trans po₂₃ˢ po[3z]ˢ)}
        z≢3 = λ{z≡3 → src-po-irreflexive (≡-sym z≡3) po[3z]ˢ}
        po[z1]ᵗ = po[⇒]ˡ z≢2 z≢3 po[z1]ˢ
        po[3z]ᵗ = po[⇒]ʳ z≢1 po[3z]ˢ
        po[zz]ᵗ = po-trans dst-wf po[z1]ᵗ (po-trans dst-wf po₁₃ᵗ po[3z]ᵗ)
    in po-irreflexive dst-wf refl po[zz]ᵗ

poˡ-3[⇐]1 : {y : Event LabelLIMM}
  → po dst ev₃ y
  → po src ev₁ y
poˡ-3[⇐]1 po[3y] =
  let y≢2 = λ{y≡2 → po-irreflexive dst-wf (≡-sym y≡2) (po-trans dst-wf po₂₃ᵗ po[3y])}
      y≢3 = λ{y≡3 → po-irreflexive dst-wf (≡-sym y≡3) po[3y]}
  in po[⇐]ʳ y≢2 y≢3 (po-trans dst-wf po₁₃ᵗ po[3y])


poˡ-1[⇒]3 : {y : Event LabelLIMM}
  → po src ev₁ y
  → po dst ev₃ y
poˡ-1[⇒]3 po[1y] =
  let y≢1 = λ{y≡1 → src-po-irreflexive (≡-sym y≡1) po[1y]}
  in po[⇒]ʳ y≢1 (src-po-trans po₃₁ˢ po[1y])


piˡ-3[⇐]1 : {y : Event LabelLIMM}
  → po-imm dst ev₃ y
  → po-imm src ev₁ y
piˡ-3[⇐]1 {y} (po[3y] , ¬∃z) = poˡ-3[⇐]1 po[3y] , ¬∃z'
  where
  ¬∃z' : ¬ (∃[ z ] po src ev₁ z × TransClosure (po src) z y)
  ¬∃z' (z , po[1z]ˢ , po⁺[zy]ˢ) =
    let po[zy]ˢ = ⁺-join-trans src-po-trans po⁺[zy]ˢ
        y≢1 = λ{y≡1 → src-po-irreflexive (≡-sym y≡1) (src-po-trans po[1z]ˢ po[zy]ˢ)}
    in ¬∃z (z , poˡ-1[⇒]3 po[1z]ˢ , [ po[⇒]ʳ y≢1 po[zy]ˢ ])


poʳ-1[⇐]2 : {x : Event LabelLIMM}
  → po dst x ev₁
  → po src x ev₂
poʳ-1[⇐]2 po[x1] =
  let x≢1 = λ{x≡1 → po-irreflexive dst-wf x≡1 po[x1]}
  in po[⇐]ˡ x≢1 (po-trans dst-wf po[x1] po₁₂ᵗ)

po₂₁ˢ : po src ev₂ ev₁
po₂₁ˢ = src-po-trans po₂₃ˢ po₃₁ˢ


piʳ-1[⇐]2 : {x : Event LabelLIMM}
  → po-imm dst x ev₁
  → po-imm src x ev₂
piʳ-1[⇐]2 {x} (po[x1] , ¬∃z) = poʳ-1[⇐]2 po[x1] , ¬∃z'
  where
  ¬∃z' : ¬ (∃[ z ] po src x z × TransClosure (po src) z ev₂)
  ¬∃z' (z , po[xz]ˢ , po⁺[z2]ˢ) =
    let po[z2]ˢ = ⁺-join-trans src-po-trans po⁺[z2]ˢ
        po[z3]ˢ = src-po-trans po[z2]ˢ po₂₃ˢ
        po[z1]ˢ = src-po-trans po[z2]ˢ po₂₁ˢ
        z≢1 = λ{z≡1 → src-po-irreflexive z≡1 po[z1]ˢ}
        z≢2 = λ{z≡2 → src-po-irreflexive z≡2 po[z2]ˢ}
        z≢3 = λ{z≡3 → src-po-irreflexive z≡3 po[z3]ˢ}
    in ¬∃z (z , po[⇒]ʳ z≢1 po[xz]ˢ , [ po[⇒]ˡ z≢2 z≢3 po[z1]ˢ ])


pi[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₂)
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → y ≢ ev₁ -- broken: pi[x1]  →  pi[x2]
  → x ≢ ev₃ -- broken: pi[3y]  →  pi[1y]
  → po-imm dst x y
  → po-imm src x y
pi[⇐] {x} {y} ¬12 ¬13 y≢1 x≢3 pi[xy]@(po[xy] , ¬∃z) with ev-eq-dec x ev₂
... | yes refl =
  let y≡3 = po-immʳ dst-wf ¬init₂ pi[xy] pi₂₃ᵗ
  in subst-rel (po-imm src) refl (≡-sym y≡3) pi₂₃ˢ
... | no x≢2 = po[⇐] ¬12 ¬13 po[xy] , ¬∃z' x≢2
  where
  ¬∃z' : x ≢ ev₂ → ¬ (∃[ z ] (po src x z × TransClosure (po src) z y))
  ¬∃z' x≢2 (z , po[xz]ˢ , po⁺[zy]ˢ) =
    let po[zy]ˢ = ⁺-join-trans src-po-trans po⁺[zy]ˢ
        po[xz]ᵗ = po[⇒] (x≢2 ∘ proj₁) (x≢3 ∘ proj₁) po[xz]ˢ
    in ¬∃z (z , po[xz]ᵗ , [ po[⇒]ʳ y≢1 po[zy]ˢ ])
    

pi[⇐]pi⁺ : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₂)
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → po-imm dst x y
  → TransClosure (po-imm src) x y
pi[⇐]pi⁺ {x} {y} ¬12 ¬13 pi[xy] with ev-eq-dec x ev₃ | ev-eq-dec y ev₁
... | yes refl | _        = pi₃₁ˢ ∷ [ piˡ-3[⇐]1 pi[xy] ]
... | no x≢3   | yes refl = piʳ-1[⇐]2 pi[xy] ∷ pi₂₃ˢ ∷ [ pi₃₁ˢ ]
... | no x≢3   | no y≢1   = [ pi[⇐] ¬12 ¬13 y≢1 x≢3 pi[xy] ]


pi⁺ˡ-3[⇐]1 : {y : Event LabelLIMM}
  → TransClosure (po-imm dst) ev₃ y
  → TransClosure (po-imm src) ev₁ y
pi⁺ˡ-3[⇐]1 [ pi[3y] ] = [ piˡ-3[⇐]1 pi[3y] ]
pi⁺ˡ-3[⇐]1 ( pi[3z] ∷ pi⁺[zy] ) =
  piˡ-3[⇐]1 pi[3z] ∷ lemma (proj₁ pi[3z]) pi⁺[zy]
  where
  pi[⇐]acc : {x y : Event LabelLIMM} → po dst ev₃ x → po-imm dst x y → po-imm src x y
  pi[⇐]acc po[3x] pi[xy] =
    let po[1x]ᵗ = po-trans dst-wf po₁₃ᵗ po[3x]
        x≢1 = λ{x≡1 → po-irreflexive dst-wf (≡-sym x≡1) po[1x]ᵗ}
        y≢1 = λ{y≡1 → po-irreflexive dst-wf (≡-sym y≡1) (po-trans dst-wf po[1x]ᵗ (proj₁ pi[xy]))}
        x≢3 = λ{x≡3 → po-irreflexive dst-wf (≡-sym x≡3) po[3x]}
    in pi[⇐] (x≢1 ∘ proj₁) (x≢1 ∘ proj₁) y≢1 x≢3 pi[xy]
  
  lemma : {x y : Event LabelLIMM}
    → po dst ev₃ x
    → TransClosure (po-imm dst) x y
    → TransClosure (po-imm src) x y
  lemma po[3x] [ pi[xy] ] = [ pi[⇐]acc po[3x] pi[xy] ]
  lemma po[3x] ( pi[xz] ∷ pi⁺[zy] ) =
    pi[⇐]acc po[3x] pi[xz] ∷ lemma (po-trans dst-wf po[3x] (proj₁ pi[xz])) pi⁺[zy]


pi⁺ʳ-1[⇐]2 : {x : Event LabelLIMM}
  → TransClosure (po-imm dst) x ev₁
  → TransClosure (po-imm src) x ev₂
pi⁺ʳ-1[⇐]2 [ pi[x1] ] = [ piʳ-1[⇐]2 pi[x1] ]
pi⁺ʳ-1[⇐]2 ( pi[xy]ᵗ ∷ pi⁺[y1]ᵗ ) =
  let po[y1]ᵗ = ⁺-join-trans (po-trans dst-wf) (⁺-map id proj₁ pi⁺[y1]ᵗ)
      po[x1]ᵗ = po-trans dst-wf (proj₁ pi[xy]ᵗ) po[y1]ᵗ
      po[x3]ᵗ = po-trans dst-wf po[x1]ᵗ po₁₃ᵗ
      x≢1 = λ{x≡1 → po-irreflexive dst-wf x≡1 po[x1]ᵗ}
      y≢1 = λ{y≡1 → po-irreflexive dst-wf y≡1 po[y1]ᵗ}
      x≢3 = λ{x≡3 → po-irreflexive dst-wf x≡3 po[x3]ᵗ}
  in pi[⇐] (x≢1 ∘ proj₁) (x≢1 ∘ proj₁) y≢1 x≢3 pi[xy]ᵗ ∷ pi⁺ʳ-1[⇐]2 pi⁺[y1]ᵗ


pi⁺[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₂)
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → TransClosure (po-imm dst) x y
  → TransClosure (po-imm src) x y
pi⁺[⇐] ¬12 ¬13 [ pi[xy]ᵗ ] = pi[⇐]pi⁺ ¬12 ¬13 pi[xy]ᵗ
pi⁺[⇐] ¬12 ¬13 ( _∷_ {x} {z} {y} pi[xz]ᵗ pi⁺[zy]ᵗ ) with ev-eq-dec x ev₁
... | yes refl = -- x ≡ 1
  let z≡2 : z ≡ ev₂ -- don't match this to refl. typechecking takes forever
      z≡2 = po-immʳ dst-wf ¬init₁ pi[xz]ᵗ pi₁₂ᵗ
  in
  case pi⁺[zy]ᵗ of
  λ{ [ pi[2y]ᵗ ] →
       let y≡3 = po-immʳ dst-wf
                   (subst (¬₁ EvInit) (≡-sym z≡2) ¬init₂)
                   pi[2y]ᵗ
                   (subst-rel (po-imm dst) (≡-sym z≡2) refl pi₂₃ᵗ)
       in ⊥-elim (¬13 (refl , y≡3))
   ; ( pi[2v]ᵗ ∷ pi⁺[vy]ᵗ ) →
         let v≡3 = po-immʳ dst-wf
                     (subst (¬₁ EvInit) (≡-sym z≡2) ¬init₂)
                     pi[2v]ᵗ
                     (subst-rel (po-imm dst) (≡-sym z≡2) refl pi₂₃ᵗ)
         in pi⁺ˡ-3[⇐]1 (subst-rel (TransClosure (po-imm dst)) v≡3 refl pi⁺[vy]ᵗ)
   }
... | no x≢1 with ×-dec (ev-eq-dec z ev₁) (ev-eq-dec y ev₂) | ×-dec (ev-eq-dec z ev₁) (ev-eq-dec y ev₃)
... | yes (refl , refl) | _ = pi⁺ʳ-1[⇐]2 [ pi[xz]ᵗ ]
... | no ¬12            | yes (refl , refl) = pi⁺ʳ-1[⇐]2 [ pi[xz]ᵗ ] ++ [ pi₂₃ˢ ]
... | no ¬12            | no ¬13 =
  pi[⇐]pi⁺ (x≢1 ∘ proj₁) (x≢1 ∘ proj₁) pi[xz]ᵗ ++ pi⁺[⇐] ¬12 ¬13 pi⁺[zy]ᵗ



udr-po[⇒] : {x : Event LabelLIMM} → x ∈ udr (po src) → x ∈ udr (po dst)
udr-po[⇒] {x} (inj₁ (y , po-dst _ _ po[xy]))  = take-udrˡ (po dst) po[xy]
udr-po[⇒] {x} (inj₁ (y , po-new₂₁ refl refl)) = take-udrˡ (po dst) po₂₃ᵗ
udr-po[⇒] {x} (inj₁ (y , po-new₃₁ refl refl)) = take-udrʳ (po dst) po₁₃ᵗ
udr-po[⇒] {y} (inj₂ (x , po-dst _ _ po[xy]))  = take-udrʳ (po dst) po[xy]
udr-po[⇒] {y} (inj₂ (x , po-new₂₁ refl refl)) = take-udrˡ (po dst) po₁₂ᵗ
udr-po[⇒] {y} (inj₂ (x , po-new₃₁ refl refl)) = take-udrˡ (po dst) po₁₂ᵗ


udr-po[⇐] : {x : Event LabelLIMM} → x ∈ udr (po dst) → x ∈ udr (po src)
udr-po[⇐] {x} (inj₁ (y , po[xy])) with ×-dec (ev-eq-dec x ev₁) (ev-eq-dec y ev₃)
... | yes (refl , refl) = take-udrʳ (po src) (po-new₂₁ refl refl)
... | no ¬13 with ×-dec (ev-eq-dec x ev₁) (ev-eq-dec y ev₂)
... | yes (refl , refl) = take-udrʳ (po src) (po-new₂₁ refl refl)
... | no ¬12 = take-udrˡ (po src) (po-dst ¬12 ¬13 po[xy])
udr-po[⇐] {y} (inj₂ (x , po[xy])) with ×-dec (ev-eq-dec x ev₁) (ev-eq-dec y ev₃)
... | yes (refl , refl) = take-udrˡ (po src) (po-new₃₁ refl refl)
... | no ¬13 with ×-dec (ev-eq-dec x ev₁) (ev-eq-dec y ev₂)
... | yes (refl , refl) = take-udrˡ (po src) (po-new₂₁ refl refl)
... | no ¬12 = take-udrʳ (po src) (po-dst ¬12 ¬13 po[xy])


-- ## Mapping: ghb

--
-- We reorder a successful RMW with a fence.
--
-- RMW ; F  →  F ; RMW
--
-- Consider the case where either `x` or `y` is in the (co)domain of the RMW.
-- In the source, it may be ordered with subsequent events by the fence.
-- However, even in the source that is /not necessary/, as the RMW does not
-- need the fence to provide this ordering; As the successful RMW acts as a
-- fence itself. So, when mapping to the target, we divert such edges away
-- from the fence.
ord[⇒] : {x y : Event LabelLIMM} → OrdAlt src x y → OrdAlt dst x y
ord[⇒] (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
  ord-init ((refl , x-init) ⨾[ _ ]⨾ po[⇒]ˡ (λ{refl → ¬init₂ x-init}) (λ{refl → ¬init₃ x-init}) po[xy] ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] {x} {y} (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz]ˢ ⨾[ z ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zy]ˢ ⨾[ _ ]⨾ (refl , y-rw)))
  with r/tag x-r
... | inj₁ x-rᵣ =
  let x≢2 = λ{x≡2 → disjoint-rₜ _ (x-rᵣ , subst EvRₐ (≡-sym x≡2) ev₂-rₐ)}
      x≢3 = λ{x≡3 → disjoint-r/w _ (x-r , subst EvW (≡-sym x≡3) ev₃-w)}
      y≢1 = λ{y≡1 → disjoint-f/rw _ (ev₁-f , subst EvRW y≡1 y-rw)}
      po[xz]ᵗ = po[⇒]ˡ x≢2 x≢3 po[xz]ˢ
      po[zy]ᵗ = po[⇒]ʳ y≢1 po[zy]ˢ
  in ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))
... | inj₂ x-rₐ =
  let po[xy]ˢ = src-po-trans po[xz]ˢ po[zy]ˢ
      y≢1 = λ{y≡1 → disjoint-f/rw _ (ev₁-f , subst EvRW y≡1 y-rw)}
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[⇒]ʳ y≢1 po[xy]ˢ ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] (ord-ww ((refl , x-w) ⨾[ x ]⨾ po[xz]ˢ ⨾[ z ]⨾ (refl , z-ww) ⨾[ _ ]⨾ po[zy]ˢ ⨾[ y ]⨾ (refl , y-w)))
  with w/tag x-w
... | inj₁ x-wᵣ = 
  let x≢2 = λ{x≡2 → disjoint-r/w _ (ev₂-r , subst EvW x≡2 x-w)}
      x≢3 = λ{x≡3 → disjoint-wₜ _ (x-wᵣ , subst EvWₐ (≡-sym x≡3) ev₃-wₐ)}
      y≢1 = λ{y≡1 → disjoint-f/w _ (ev₁-f , subst EvW y≡1 y-w)}
      po[xz]ᵗ = po[⇒]ˡ x≢2 x≢3 po[xz]ˢ
      po[zy]ᵗ = po[⇒]ʳ y≢1 po[zy]ˢ
  in ord-ww ((refl , x-w) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , z-ww) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , y-w))
... | inj₂ x-wₐ =
  let x∈src = poˡ∈src po[xz]ˢ
      x∈rmwʳ = ⇔₁-apply-⊇₁ (rmw-w dst-wf) (x∈src , x-wₐ)
      po[xy]ˢ = src-po-trans po[xz]ˢ po[zy]ˢ
      y≢1 = λ{y≡1 → disjoint-f/w _ (ev₁-f , subst EvW y≡1 y-w)}
      po[xy]ᵗ = po[⇒]ʳ y≢1 po[xy]ˢ
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , w⇒rw y-w))
ord[⇒] (ord-sc ((refl , x-rw) ⨾[ x ]⨾ po[xz]ˢ ⨾[ z ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy]ˢ ⨾[ y ]⨾ (refl , y-rw)))
  with rw/tag x-rw
... | inj₁ x-rwᵣ =
  let x≢2 = λ{x≡2 → disjoint-rwₜ _ (subst (EvRWₜ tmov) x≡2 x-rwᵣ , rₜ⇒rwₜ ev₂-rₐ)}
      x≢3 = λ{x≡3 → disjoint-rwₜ _ (subst (EvRWₜ tmov) x≡3 x-rwᵣ , wₜ⇒rwₜ ev₃-wₐ)}
      po[xz]ᵗ = po[⇒]ˡ x≢2 x≢3 po[xz]ˢ
      y≢1 = λ{y≡1 → disjoint-f/rw _ (ev₁-f , subst EvRW y≡1 y-rw)}
      po[zy]ᵗ = po[⇒]ʳ y≢1 po[zy]ˢ
  in ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))
... | inj₂ x-rwₐ with rwₜ/rw x-rwₐ
... | inj₁ x-rₐ =
  let po[xy]ˢ = src-po-trans po[xz]ˢ po[zy]ˢ
      y≢1 = λ{y≡1 → disjoint-f/rw _ (ev₁-f , subst EvRW y≡1 y-rw)}
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[⇒]ʳ y≢1 po[xy]ˢ ⨾[ _ ]⨾ (refl , y-rw))
... | inj₂ x-wₐ =
  let x∈src = poˡ∈src po[xz]ˢ
      x∈rmwʳ = ⇔₁-apply-⊇₁ (rmw-w dst-wf) (x∈src , x-wₐ)
      po[xy]ˢ = src-po-trans po[xz]ˢ po[zy]ˢ
      y≢1 = λ{y≡1 → disjoint-f/rw _ (ev₁-f , subst EvRW y≡1 y-rw)}
      po[xy]ᵗ = po[⇒]ʳ y≢1 po[xy]ˢ
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] (ord-rmw-dom ((refl , x-rw) ⨾[ x ]⨾ po[xy]ˢ ⨾[ y ]⨾ (refl , y∈rmwˡ))) =
  let y-r = rₜ⇒r (rmwˡ-r dst-wf y∈rmwˡ)
      po[xy]ᵗ = po[⇒]ʳ  (λ{y≡1 → disjoint-f/r _ (ev₁-f , subst EvR y≡1 y-r)}) po[xy]ˢ
  in ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y∈rmwˡ))
ord[⇒] (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xy]ˢ ⨾[ y ]⨾ (refl , y-rw))) =
  let po[xy]ᵗ = po[⇒]ʳ (λ{y≡1 → disjoint-f/rw _ (ev₁-f , subst EvRW y≡1 y-rw)}) po[xy]ˢ
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy]ˢ ⨾[ y ]⨾ (refl , y-wₐ))) =
  let po[xy]ᵗ = po[⇒]ʳ (λ{y≡1 → disjoint-f/w _ (ev₁-f , subst EvW y≡1 (wₜ⇒w y-wₐ))}) po[xy]ˢ
  in ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-wₐ))
ord[⇒] (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy]ˢ ⨾[ _ ]⨾ (refl , y-rw))) =
  let po[xy]ᵗ = po[⇒]ʳ (λ{y≡1 → disjoint-f/rw _ (ev₁-f , (subst EvRW y≡1 y-rw))}) po[xy]ˢ
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-rw))

¬po[⇒] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₂)
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → ¬ po src x y → ¬ po dst x y
¬po[⇒] ¬12 ¬13 ¬po[xy]ˢ = ¬po[xy]ˢ ∘ po[⇐] ¬12 ¬13

¬po[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₂ × y ≡ ev₁)
  → ¬ (x ≡ ev₃ × y ≡ ev₁)
  → ¬ po dst x y
  → ¬ po src x y
¬po[⇐] ¬21 ¬31 ¬po[xy]ᵗ = ¬po[xy]ᵗ ∘ po[⇒] ¬21 ¬31

¬po[⇐]ˡ : {x y : Event LabelLIMM}
  → x ≢ ev₂
  → x ≢ ev₃
  → ¬ po dst x y
  → ¬ po src x y
¬po[⇐]ˡ x≢2 x≢3 = ¬po[⇐] (x≢2 ∘ proj₁) (x≢3 ∘ proj₁)

¬po[⇐]ʳ : {x y : Event LabelLIMM}
  → y ≢ ev₁
  → ¬ po dst x y
  → ¬ po src x y
¬po[⇐]ʳ y≢1 = ¬po[⇐] (y≢1 ∘ proj₂) (y≢1 ∘ proj₂)

rfe[⇒] : {x y : Event LabelLIMM} → rfe src x y → rfe dst x y
rfe[⇒] (rf[xy] , ¬po[xy]) =
  let x≢1 = λ{x≡1 → disjoint-f/w _ (ev₁-f , subst EvW x≡1 (×₂-applyˡ (rf-w×r dst-wf) rf[xy]))}
  in rf[xy] , ¬po[⇒] (x≢1 ∘ proj₁) (x≢1 ∘ proj₁) ¬po[xy]

coe[⇒] : {x y : Event LabelLIMM} → coe src x y → coe dst x y
coe[⇒] (co[xy] , ¬po[xy]) =
  let x≢1 = λ{x≡1 → disjoint-f/w _ (ev₁-f , subst EvW x≡1 (×₂-applyˡ (co-w×w dst-wf) co[xy]))}
  in co[xy] , ¬po[⇒] (x≢1 ∘ proj₁) (x≢1 ∘ proj₁) ¬po[xy]

fre[⇒] : {x y : Event LabelLIMM} → fre src x y → fre dst x y
fre[⇒] (fr[xy] , ¬po[xy]) =
  let x≢1 = λ{x≡1 → disjoint-f/r _ (ev₁-f , subst EvR x≡1 (×₂-applyˡ (fr-r×w dst-wf) fr[xy]))}
  in fr[xy] , ¬po[⇒] (x≢1 ∘ proj₁) (x≢1 ∘ proj₁) ¬po[xy]


ghbi[⇒] : {x y : Event LabelLIMM} → GhbiAlt src x y → GhbiAlt dst x y
ghbi[⇒] (ghbi-ord ord[xy]) = ghbi-ord (ord[⇒] ord[xy])
ghbi[⇒] (ghbi-rfe rfe[xy]) = ghbi-rfe (rfe[⇒] rfe[xy])
ghbi[⇒] (ghbi-coe coe[xy]) = ghbi-coe (coe[⇒] coe[xy])
ghbi[⇒] (ghbi-fre fre[xy]) = ghbi-fre (fre[⇒] fre[xy])
