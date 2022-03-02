{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder12 using (ReorderRestricted12)


-- |
--
module Proof.Reorder.Reorder12.Execution
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted12 dst)
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
open ReorderRestricted12 dst-res
open TransformReorder12.Extra dst-res

--
-- Most of this modules consists of the many lemmas & sub-proofs for `pi⁺[⇐]`.
--

dst-ok : IsLIMMConsistent dst
dst-ok = consistent

dst-wf : WellFormed dst
dst-wf = wellformed


-- # Definitions

--
--
-- Consider the `po` target po sequence:
--
-- a (1 2) 3 b
--
-- In the source this becomes:
--
-- a 3 (1 2) b
--
-- When constructing the source, we break: `po 1 3` and `po 2 3`.
-- And we add `po 3 1` and `po 2 1`. Any relations outside 1, 2, and 3
-- remain unchanged.
data SrcPo (x y : Event LabelLIMM) : Set where
  po-dst : ¬ (x ≡ ev₁ × y ≡ ev₃) → ¬ (x ≡ ev₂ × y ≡ ev₃) → po dst x y → SrcPo x y
  po-new₃₁ : x ≡ ev₃ → y ≡ ev₁ → SrcPo x y
  po-new₃₂ : x ≡ ev₃ → y ≡ ev₂ → SrcPo x y

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

src-po-irreflexive : Irreflexive _≡_ SrcPo
src-po-irreflexive refl (po-new₃₁ refl refl) = ⊥-elim (ev₁≢ev₃ refl)
src-po-irreflexive refl (po-new₃₂ refl refl) = ⊥-elim (ev₂≢ev₃ refl)
src-po-irreflexive refl (po-dst _ _ po[xy])  = po-irreflexive dst-wf refl po[xy]


src-po-trans : Transitive SrcPo
src-po-trans {x} {y} {z} (po-dst ¬13₁ ¬23₁ po[xy]) (po-dst ¬13₂ ¬23₂ po[yz]) =
  po-dst
    (λ{(x≡1@refl , z≡3@refl) → ¬23₂ (lemma po[xy] po[yz] , z≡3)})
    (λ{(x≡2@refl , z≡3@refl) → proj₂ pi₂₃ᵗ (_ , po[xy] , [ po[yz] ])})
    (po-trans dst-wf po[xy] po[yz])
  where
  lemma : po dst ev₁ y → po dst y ev₃ → y ≡ ev₂
  lemma po[1y] po[y3] =
    ⊎⊥-elim id
      (λ{po[y2] → proj₂ pi₁₂ᵗ (_ , po[1y] , [ po[y2] ])})
      (unsplit-poʳ dst-wf po[y3] pi₂₃ᵗ)
src-po-trans (po-dst ¬13 ¬23 po[x3]) (po-new₃₁ refl refl) = -- goal: po src x ev₁
  let x≢1 = λ{x≡1 → ¬13 (x≡1 , refl)}
      x≢2 = λ{x≡2 → ¬23 (x≡2 , refl)}
      po[x2] = ⊥⊎-elim x≢2 id (unsplit-poʳ dst-wf po[x3] pi₂₃ᵗ)
      po[x1] = ⊥⊎-elim x≢1 id (unsplit-poʳ dst-wf po[x2] pi₁₂ᵗ)
  in po-dst (ev₁≢ev₃ ∘ proj₂) (ev₁≢ev₃ ∘ proj₂) po[x1]
src-po-trans (po-dst ¬13 ¬23 po[x3]) (po-new₃₂ refl refl) = -- goal: po[x2]
  let x≢2 = λ{x≡2 → ¬23 (x≡2 , refl)}
      po[x2] = ⊥⊎-elim x≢2 id (unsplit-poʳ dst-wf po[x3] pi₂₃ᵗ)
  in po-dst (ev₂≢ev₃ ∘ proj₂) (ev₂≢ev₃ ∘ proj₂) po[x2]
src-po-trans {x} {y} {z} (po-new₃₁ refl refl) (po-dst ¬13 ¬23 po[1z])
  with unsplit-poˡ dst-wf ¬init₁ po[1z] pi₁₂ᵗ
... | inj₁ z≡2 = po-new₃₂ refl (≡-sym z≡2)
... | inj₂ po[2z] = -- goal: po[3z]
  let z≢3 = λ{z≡3 → ¬13 (refl , z≡3)}
      po[3z] = ⊥⊎-elim (≢-sym z≢3) id (unsplit-poˡ dst-wf ¬init₂ po[2z] pi₂₃ᵗ)
  in po-dst (z≢3 ∘ proj₂) (z≢3 ∘ proj₂) po[3z]
src-po-trans (po-new₃₂ refl refl) (po-dst ¬13 ¬23 po[2z]) = -- goal: po[3z]
  let z≢3 = λ{z≡3 → ¬23 (refl , z≡3)}
      po[3z] = ⊥⊎-elim (≢-sym z≢3) id (unsplit-poˡ dst-wf ¬init₂ po[2z] pi₂₃ᵗ)
  in po-dst (z≢3 ∘ proj₂) (z≢3 ∘ proj₂) po[3z]
-- impossible cases
src-po-trans (po-new₃₁ refl refl) (po-new₃₂ refl refl) = ⊥-elim (ev₁≢ev₃ refl)
src-po-trans (po-new₃₁ refl refl) (po-new₃₁ refl refl) = ⊥-elim (ev₁≢ev₃ refl)
src-po-trans (po-new₃₂ refl refl) (po-new₃₁ refl refl) = ⊥-elim (ev₂≢ev₃ refl)
src-po-trans (po-new₃₂ refl refl) (po-new₃₂ refl refl) = ⊥-elim (ev₂≢ev₃ refl)


poˡ∈src : {x y : Event LabelLIMM} → po src x y → x ∈ events src
poˡ∈src (po-new₃₂ refl _)   = ev₃∈ex
poˡ∈src (po-new₃₁ refl _)   = ev₃∈ex
poˡ∈src (po-dst _ _ po[xy]) = poˡ∈ex dst-wf po[xy]

poʳ∈src : {x y : Event LabelLIMM} → po src x y → y ∈ events src
poʳ∈src (po-new₃₂ _ refl)   = ev₂∈ex
poʳ∈src (po-new₃₁ _ refl)   = ev₁∈ex
poʳ∈src (po-dst _ _ po[xy]) = poʳ∈ex dst-wf po[xy]


-- # Mapping

-- ## Mapping: po

po[⇒] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₃ × y ≡ ev₁)
  → ¬ (x ≡ ev₃ × y ≡ ev₂)
  → po src x y
    ---------------------
  → po dst x y
po[⇒] ¬31 ¬32 (po-new₃₁ x≡3 y≡3)  = ⊥-elim (¬31 (x≡3 , y≡3))
po[⇒] ¬31 ¬32 (po-new₃₂ x≡3 y≡2)  = ⊥-elim (¬32 (x≡3 , y≡2))
po[⇒] ¬31 ¬32 (po-dst _ _ po[xy]) = po[xy]

po[⇒]ˡ : {x y : Event LabelLIMM}
  → x ≢ ev₃
  → po src x y
    ----------
  → po dst x y
po[⇒]ˡ x≢3 = po[⇒] (x≢3 ∘ proj₁) (x≢3 ∘ proj₁)

po[⇒]ʳ : {x y : Event LabelLIMM}
  → y ≢ ev₁
  → y ≢ ev₂
  → po src x y
    ----------
  → po dst x y
po[⇒]ʳ y≢1 y≢2 = po[⇒] (y≢1 ∘ proj₂) (y≢2 ∘ proj₂)


po[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → ¬ (x ≡ ev₂ × y ≡ ev₃)
  → po dst x y
    -------------------------------------------
  → po src x y
po[⇐] = po-dst

po[⇐]ˡ : {x y : Event LabelLIMM}
  → x ≢ ev₁
  → x ≢ ev₂
  → po dst x y
    ----------
  → po src x y
po[⇐]ˡ x≢1 x≢2 = po[⇐] (x≢1 ∘ proj₁) (x≢2 ∘ proj₁)

po[⇐]ʳ : {x y : Event LabelLIMM}
  → y ≢ ev₃
  → po dst x y
    -------------------------------------------
  → po src x y
po[⇐]ʳ y≢3 = po[⇐] (y≢3 ∘ proj₂) (y≢3 ∘ proj₂)

po₃₁ˢ : po src ev₃ ev₁
po₃₁ˢ = po-new₃₁ refl refl

po₃₂ˢ : po src ev₃ ev₂
po₃₂ˢ = po-new₃₂ refl refl

po₁₂ˢ : po src ev₁ ev₂
po₁₂ˢ = po-dst (ev₂≢ev₃ ∘ proj₂) (ev₂≢ev₃ ∘ proj₂) po₁₂ᵗ

pi₁₂ˢ : po-imm src ev₁ ev₂
pi₁₂ˢ = po₁₂ˢ , ¬∃z
  where
  ¬∃z : ¬ (∃[ z ] (po src ev₁ z × TransClosure (po src) z ev₂))
  ¬∃z (z , po[1z]ˢ , po⁺[z2]ˢ) =
    let po[z2]ˢ = ⁺-join-trans src-po-trans po⁺[z2]ˢ
        z≢1 = λ{z≡1 → src-po-irreflexive (≡-sym z≡1) po[1z]ˢ}
        z≢2 = λ{z≡2 → src-po-irreflexive z≡2 po[z2]ˢ}
        z≢3 = λ{z≡3 → src-po-irreflexive (≡-sym z≡3) (src-po-trans po₃₁ˢ po[1z]ˢ)}
        po[1z]ᵗ = po[⇒]ʳ z≢1 z≢2 po[1z]ˢ
        po[z2]ᵗ = po[⇒]ˡ z≢3 po[z2]ˢ
    in proj₂ pi₁₂ᵗ (z , po[1z]ᵗ , [ po[z2]ᵗ ])

pi₃₁ˢ : po-imm src ev₃ ev₁
pi₃₁ˢ = po₃₁ˢ , ¬∃z
  where
  ¬∃z : ¬ (∃[ z ] (po src ev₃ z × TransClosure (po src) z ev₁))
  ¬∃z (z , po[3z]ˢ , po⁺[z1]ˢ) =
    let po[z1]ˢ = ⁺-join-trans src-po-trans po⁺[z1]ˢ
        z≢1 = λ{z≡1 → src-po-irreflexive z≡1 po[z1]ˢ}
        z≢2 = λ{z≡2 → src-po-irreflexive z≡2 (src-po-trans po[z1]ˢ po₁₂ˢ)}
        z≢3 = λ{z≡3 → src-po-irreflexive (≡-sym z≡3) po[3z]ˢ}
        po[3z]ᵗ = po[⇒]ʳ z≢1 z≢2 po[3z]ˢ
        po[z1]ᵗ = po[⇒]ˡ z≢3 po[z1]ˢ
        po[zz]ᵗ = po-trans dst-wf po[z1]ᵗ (po-trans dst-wf po₁₃ᵗ po[3z]ᵗ)
    in po-irreflexive dst-wf refl po[zz]ᵗ

poˡ-3[⇐]2 : {y : Event LabelLIMM}
  → po dst ev₃ y
  → po src ev₂ y
poˡ-3[⇐]2 po[3y] =
  let y≢3 = λ{y≡3 → po-irreflexive dst-wf (≡-sym y≡3) po[3y]}
  in po[⇐]ʳ y≢3 (po-trans dst-wf po₂₃ᵗ po[3y])


poˡ-2[⇒]3 : {y : Event LabelLIMM}
  → po src ev₂ y
  → po dst ev₃ y
poˡ-2[⇒]3 po[2y] =
  let y≢1 = λ{y≡1 → src-po-irreflexive (≡-sym y≡1) (src-po-trans po₁₂ˢ po[2y])}
      y≢2 = λ{y≡2 → src-po-irreflexive (≡-sym y≡2) po[2y]}
  in po[⇒]ʳ y≢1 y≢2 (src-po-trans po₃₂ˢ po[2y])


poʳ-3[⇒]1 : {x : Event LabelLIMM}
  → po src x ev₃
  → po dst x ev₁
poʳ-3[⇒]1 po[x3] =
  let x≢3 = λ{x≡3 → src-po-irreflexive x≡3 po[x3]}
  in po[⇒]ˡ x≢3 (src-po-trans po[x3] po₃₁ˢ)


piˡ-3[⇐]2 : {y : Event LabelLIMM}
  → po-imm dst ev₃ y
  → po-imm src ev₂ y
piˡ-3[⇐]2 {y} (po[3y] , ¬∃z) = poˡ-3[⇐]2 po[3y] , ¬∃z' -- poˡ-3[⇐]1 po[3y] , ¬∃z'
  where
  ¬∃z' : ¬ (∃[ z ] po src ev₂ z × TransClosure (po src) z y)
  ¬∃z' (z , po[2z]ˢ , po⁺[zy]ˢ) =
    let po[zy]ˢ = ⁺-join-trans src-po-trans po⁺[zy]ˢ
        z≢3 = λ{z≡3 → src-po-irreflexive (≡-sym z≡3) (src-po-trans po₃₂ˢ po[2z]ˢ)}
    in ¬∃z (z , poˡ-2[⇒]3 po[2z]ˢ , [ po[⇒]ˡ z≢3 po[zy]ˢ ])


poʳ-1[⇐]3 : {x : Event LabelLIMM}
  → po dst x ev₁
  → po src x ev₃
poʳ-1[⇐]3 po[x1]ᵗ =
  let x≢1 = λ{x≡1 → po-irreflexive dst-wf x≡1 po[x1]ᵗ}
      x≢2 = λ{x≡2 → po-irreflexive dst-wf x≡2 (po-trans dst-wf po[x1]ᵗ po₁₂ᵗ)}
  in po[⇐]ˡ x≢1 x≢2 (po-trans dst-wf po[x1]ᵗ po₁₃ᵗ)


-- target: x  (1 2) 3
-- source: x  3 (1 2)
--
-- piᵗ x 1  →  piˢ x 3
piʳ-1[⇐]3 : {x : Event LabelLIMM}
  → po-imm dst x ev₁
  → po-imm src x ev₃
piʳ-1[⇐]3 {x} (po[x1]ᵗ , ¬∃z) = poʳ-1[⇐]3 po[x1]ᵗ , ¬∃z'
  where
  ¬∃z' : ¬ (∃[ z ] po src x z × TransClosure (po src) z ev₃)
  ¬∃z' (z , po[xz]ˢ , po⁺[z3]ˢ) =
    let po[z3]ˢ = ⁺-join-trans src-po-trans po⁺[z3]ˢ
        x≢3 = λ{x≡3 → src-po-irreflexive x≡3 (src-po-trans po[xz]ˢ po[z3]ˢ)}
    in ¬∃z (z , po[⇒]ˡ x≢3 po[xz]ˢ , [ poʳ-3[⇒]1 po[z3]ˢ ])


pi[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → ¬ (x ≡ ev₂ × y ≡ ev₃)
  → y ≢ ev₁ -- broken: pi[x1]  →  pi[x2]
  → x ≢ ev₃ -- broken: pi[3y]  →  pi[1y]
  → po-imm dst x y
  → po-imm src x y
pi[⇐] {x} {y} ¬13 ¬23 y≢1 x≢3 pi[xy]ᵗ@(po[xy]ᵗ , ¬∃z) with ev-eq-dec y ev₂
... | yes refl = -- y ≡ 2 → x ≡ 1
  let x≡1 = po-immˡ dst-wf pi[xy]ᵗ pi₁₂ᵗ
  in subst-rel (po-imm src) (≡-sym x≡1) refl pi₁₂ˢ
... | no y≢2 = po[⇐] ¬13 ¬23 po[xy]ᵗ , ¬∃z' y≢2
  where
  ¬∃z' : y ≢ ev₂ → ¬ (∃[ z ] (po src x z × TransClosure (po src) z y))
  ¬∃z' y≢2 (z , po[xz]ˢ , po⁺[zy]ˢ) =
    let po[zy]ˢ = ⁺-join-trans src-po-trans po⁺[zy]ˢ
        po[zy]ᵗ = po[⇒] (y≢1 ∘ proj₂) (y≢2 ∘ proj₂) po[zy]ˢ
    in ¬∃z (z , po[⇒]ˡ x≢3 po[xz]ˢ , [ po[zy]ᵗ ])
    

-- target: x (1 2) 3 y
-- source: x 3 (1 2) y
--
-- piᵗ 3 y  →  piˢ 3 1 ∷ piˢ 1 2 ∷ piˢ 2 y
-- piᵗ x 1  →  piˢ x 3 ∷ piˢ 3 1
pi[⇐]pi⁺ : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → ¬ (x ≡ ev₂ × y ≡ ev₃)
  → po-imm dst x y
  → TransClosure (po-imm src) x y
pi[⇐]pi⁺ {x} {y} ¬13 ¬23 pi[xy] with ev-eq-dec x ev₃ | ev-eq-dec y ev₁
... | yes refl | _        = pi₃₁ˢ ∷ pi₁₂ˢ ∷ [ piˡ-3[⇐]2 pi[xy] ]
... | no x≢3   | yes refl = piʳ-1[⇐]3 pi[xy] ∷ [ pi₃₁ˢ ]
... | no x≢3   | no y≢1   = [ pi[⇐] ¬13 ¬23 y≢1 x≢3 pi[xy] ]


pi⁺ˡ-3[⇐]2 : {y : Event LabelLIMM}
  → TransClosure (po-imm dst) ev₃ y
  → TransClosure (po-imm src) ev₂ y
pi⁺ˡ-3[⇐]2 [ pi[3y] ] = [ piˡ-3[⇐]2 pi[3y] ]
pi⁺ˡ-3[⇐]2 {y} ( pi[3z] ∷ pi⁺[zy] ) = piˡ-3[⇐]2 pi[3z] ∷ lemma (proj₁ pi[3z]) pi⁺[zy]
  where
  pi[⇐]acc : {x y : Event LabelLIMM} → po dst ev₃ x → po-imm dst x y → po-imm src x y
  pi[⇐]acc po[3x]ᵗ pi[xy]ᵗ =
    let po[1x]ᵗ = po-trans dst-wf po₁₃ᵗ po[3x]ᵗ
        x≢3 = λ{x≡3 → po-irreflexive dst-wf (≡-sym x≡3) po[3x]ᵗ}
        y≢1 = λ{y≡1 → po-irreflexive dst-wf (≡-sym y≡1) (po-trans dst-wf po[1x]ᵗ (proj₁ pi[xy]ᵗ))}
        y≢3 = λ{y≡3 → po-irreflexive dst-wf (≡-sym y≡3) (po-trans dst-wf po[3x]ᵗ (proj₁ pi[xy]ᵗ))}
    in pi[⇐] (y≢3 ∘ proj₂) (y≢3 ∘ proj₂) y≢1 x≢3 pi[xy]ᵗ
  
  lemma : {x : Event LabelLIMM} → po dst ev₃ x → TransClosure (po-imm dst) x y → TransClosure (po-imm src) x y
  lemma po[3x] [ pi[xy] ] = [ pi[⇐]acc po[3x] pi[xy] ]
  lemma po[3x] ( pi[xz] ∷ pi⁺[zy] ) =
    pi[⇐]acc po[3x] pi[xz] ∷ lemma (po-trans dst-wf po[3x] (proj₁ pi[xz])) pi⁺[zy]


pi⁺[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → ¬ (x ≡ ev₂ × y ≡ ev₃)
  → TransClosure (po-imm dst) x y
  → TransClosure (po-imm src) x y
pi⁺[⇐] ¬13 ¬23 [ pi[xy]ᵗ ] = pi[⇐]pi⁺ ¬13 ¬23 pi[xy]ᵗ
pi⁺[⇐] ¬13 ¬23 ( _∷_ {x} {z} {y} pi[xz]ᵗ pi⁺[zy]ᵗ )
  with ev-eq-dec z ev₃
... | yes refl = -- z ≡ 3
  let x≡2 = po-immˡ dst-wf pi[xz]ᵗ pi₂₃ᵗ
  in subst-rel (TransClosure (po-imm src)) (≡-sym x≡2) refl (pi⁺ˡ-3[⇐]2 pi⁺[zy]ᵗ)
... | no z≢3 with ×-dec (ev-eq-dec z ev₁) (ev-eq-dec y ev₃)
... | yes (refl , refl) = [ piʳ-1[⇐]3 pi[xz]ᵗ ]
... | no ¬13₂ =
  let ¬23 = λ{(z≡2@refl , y≡3) →
                let x≡1 = po-immˡ dst-wf pi[xz]ᵗ pi₁₂ᵗ
                in ¬13 (x≡1 , y≡3)}
  in pi[⇐]pi⁺ (z≢3 ∘ proj₂) (z≢3 ∘ proj₂) pi[xz]ᵗ ++ pi⁺[⇐] ¬13₂ ¬23 pi⁺[zy]ᵗ


udr-po[⇒] : {x : Event LabelLIMM} → x ∈ udr (po src) → x ∈ udr (po dst)
udr-po[⇒] {x} (inj₁ (y , po-dst _ _ po[xy]))  = take-udrˡ (po dst) po[xy]
udr-po[⇒] {x} (inj₁ (y , po-new₃₁ refl refl)) = take-udrʳ (po dst) po₂₃ᵗ
udr-po[⇒] {x} (inj₁ (y , po-new₃₂ refl refl)) = take-udrʳ (po dst) po₂₃ᵗ
udr-po[⇒] {x} (inj₂ (y , po-dst _ _ po[yx]))  = take-udrʳ (po dst) po[yx]
udr-po[⇒] {x} (inj₂ (y , po-new₃₁ refl refl)) = take-udrˡ (po dst) po₁₂ᵗ
udr-po[⇒] {x} (inj₂ (y , po-new₃₂ refl refl)) = take-udrʳ (po dst) po₁₂ᵗ


udr-po[⇐] : {x : Event LabelLIMM} → x ∈ udr (po dst) → x ∈ udr (po src)
udr-po[⇐] {x} (inj₁ (y , po[xy])) with ×-dec (ev-eq-dec x ev₁) (ev-eq-dec y ev₃)
... | yes (refl , refl) = take-udrˡ (po src) po₁₂ˢ
... | no ¬13 with ×-dec (ev-eq-dec x ev₂) (ev-eq-dec y ev₃)
... | yes (refl , refl) = take-udrʳ (po src) po₁₂ˢ
... | no ¬23 = take-udrˡ (po src) (po-dst ¬13 ¬23 po[xy])
udr-po[⇐] {y} (inj₂ (x , po[xy])) with ×-dec (ev-eq-dec x ev₁) (ev-eq-dec y ev₃)
... | yes (refl , refl) = take-udrˡ (po src) po₃₁ˢ
... | no ¬13 with ×-dec (ev-eq-dec x ev₂) (ev-eq-dec y ev₃)
... | yes (refl , refl) = take-udrˡ (po src) po₃₁ˢ
... | no ¬23 = take-udrʳ (po src) (po-dst ¬13 ¬23 po[xy])


-- ## Mapping: ghb

--
-- We reorder a successful RMW with a fence.
--
-- F ; RMW  →  RMW ; F
--
-- Consider the case where either `x` or `y` is in the (co)domain of the RMW.
-- In the source, it may be ordered with preceding events by the fence.
-- However, even in the source that is /not necessary/, as the RMW does not
-- need the fence to provide this ordering; As the successful RMW acts as a
-- fence itself. So, when mapping to the target, we divert such edges away
-- from the fence.
ord[⇒] : {x y : Event LabelLIMM} → OrdAlt src x y → OrdAlt dst x y
ord[⇒] (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
  let x≢3 = λ{x≡3 → disjoint-f/init _ (ev₃-f , subst EvInit x≡3 x-init)}
  in ord-init ((refl , x-init) ⨾[ _ ]⨾ po[⇒]ˡ x≢3 po[xy] ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] (ord-rm ((refl , x-r) ⨾[ x ]⨾ po[xy]ˢ ⨾[ y ]⨾ (refl , y-rm) ⨾[ _ ]⨾ po[yz]ˢ ⨾[ z ]⨾ (refl , z-rw)))
  with ev-eq-dec z ev₁ | ev-eq-dec z ev₂
... | yes refl | _       =
  let po[xy]ˢ = src-po-trans po[xy]ˢ po[yz]ˢ
      x≢3 = λ{x≡3 → disjoint-f/r _ (ev₃-f , subst EvR x≡3 x-r)}
      po[xy]ᵗ = po[⇒]ˡ x≢3 po[xy]ˢ
  in ord-rmw-dom ((refl , r⇒rw x-r) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , take-dom (rmw dst) rmw₁₂ᵗ))
... | no  z≢1  | yes refl =
  let po[xy]ˢ = src-po-trans po[xy]ˢ po[yz]ˢ
      x≢3 = λ{x≡3 → disjoint-f/r _ (ev₃-f , subst EvR x≡3 x-r)}
      po[xy]ᵗ = po[⇒]ˡ x≢3 po[xy]ˢ
  in ord-w ((refl , r⇒rw x-r) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , ev₂-wₐ))
... | no  z≢1  | no  z≢2  =
  let x≢3 = λ{x≡3 → disjoint-f/r _ (ev₃-f , subst EvR x≡3 x-r)}
      po[xy]ᵗ = po[⇒]ˡ x≢3 po[xy]ˢ
      po[yz]ᵗ = po[⇒]ʳ z≢1 z≢2 po[yz]ˢ
  in ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-rm) ⨾[ _ ]⨾ po[yz]ᵗ ⨾[ _ ]⨾ (refl , z-rw))
ord[⇒] (ord-ww ((refl , x-w) ⨾[ x ]⨾ po[xy]ˢ ⨾[ y ]⨾ (refl , y-ww) ⨾[ _ ]⨾ po[yz]ˢ ⨾[ z ]⨾ (refl , z-w)))
  with ev-eq-dec z ev₂
... | yes refl =
  let po[xy]ˢ = src-po-trans po[xy]ˢ po[yz]ˢ
      x≢3 = λ{x≡3 → disjoint-f/w _ (ev₃-f , subst EvW x≡3 x-w)}
      po[xy]ᵗ = po[⇒]ˡ x≢3 po[xy]ˢ
  in ord-w ((refl , w⇒rw x-w) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , ev₂-wₐ))
... | no  z≢2  =
  let x≢3 = λ{x≡3 → disjoint-f/w _ (ev₃-f , subst EvW x≡3 x-w)}
      z≢1 = λ{z≡2 → disjoint-r/w _ (ev₁-r , subst EvW z≡2 z-w)}
      po[xy]ᵗ = po[⇒]ˡ x≢3 po[xy]ˢ
      po[yz]ᵗ = po[⇒]ʳ z≢1 z≢2 po[yz]ˢ
  in ord-ww ((refl , x-w) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-ww) ⨾[ _ ]⨾ po[yz]ᵗ ⨾[ _ ]⨾ (refl , z-w))
ord[⇒] (ord-sc ((refl , x-rw) ⨾[ x ]⨾ po[xy]ˢ ⨾[ y ]⨾ (refl , y-sc) ⨾[ _ ]⨾ po[yz]ˢ ⨾[ z ]⨾ (refl , z-rw)))
  with ev-eq-dec z ev₁ | ev-eq-dec z ev₂
... | yes refl | _       =
  let po[xy]ˢ = src-po-trans po[xy]ˢ po[yz]ˢ
      x≢3 = λ{x≡3 → disjoint-f/rw _ (ev₃-f , subst EvRW x≡3 x-rw)}
      po[xy]ᵗ = po[⇒]ˡ x≢3 po[xy]ˢ
  in ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , take-dom (rmw dst) rmw₁₂ᵗ))
... | no  z≢1  | yes refl =
  let po[xy]ˢ = src-po-trans po[xy]ˢ po[yz]ˢ
      x≢3 = λ{x≡3 → disjoint-f/rw _ (ev₃-f , subst EvRW x≡3 x-rw)}
      po[xy]ᵗ = po[⇒]ˡ x≢3 po[xy]ˢ
  in ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , ev₂-wₐ))
... | no  z≢1  | no  z≢2  =
  let x≢3 = λ{x≡3 → disjoint-f/rw _ (ev₃-f , subst EvRW x≡3 x-rw)}
      po[xy]ᵗ = po[⇒]ˡ x≢3 po[xy]ˢ
      po[yz]ᵗ = po[⇒]ʳ z≢1 z≢2 po[yz]ˢ
  in ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xy]ᵗ ⨾[ _ ]⨾ (refl , y-sc) ⨾[ _ ]⨾ po[yz]ᵗ ⨾[ _ ]⨾ (refl , z-rw))
ord[⇒] (ord-rmw-dom ((refl , x-rw) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y∈rmwˡ))) =
  let x≢3 = λ{x≡3 → disjoint-f/rw _ (ev₃-f , subst EvRW x≡3 x-rw)}
  in ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[⇒]ˡ x≢3 po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ))
ord[⇒] (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
  let x≢3 = λ{x≡3 → disjoint-f/w _ (ev₃-f , subst EvW x≡3 (wₜ⇒w (rmwʳ-w dst-wf x∈rmwʳ)))}
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[⇒]ˡ x≢3 po[xy] ⨾[ _ ]⨾ (refl , y-rw))
ord[⇒] (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-wₐ))) =
  let x≢3 = λ{x≡3 → disjoint-f/rw _ (ev₃-f , subst EvRW x≡3 x-rw)}
  in ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[⇒]ˡ x≢3 po[xy] ⨾[ _ ]⨾ (refl , y-wₐ))
ord[⇒] (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
  let x≢3 = λ{x≡3 → disjoint-f/r _ (ev₃-f , subst EvR x≡3 (rₜ⇒r x-rₐ))}
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[⇒]ˡ x≢3 po[xy] ⨾[ _ ]⨾ (refl , y-rw))
  
¬po[⇒] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₁ × y ≡ ev₃)
  → ¬ (x ≡ ev₂ × y ≡ ev₃)
  → ¬ po src x y → ¬ po dst x y
¬po[⇒] ¬13 ¬23 ¬po[xy]ˢ = ¬po[xy]ˢ ∘ po[⇐] ¬13 ¬23


¬po[⇐] : {x y : Event LabelLIMM}
  → ¬ (x ≡ ev₃ × y ≡ ev₁)
  → ¬ (x ≡ ev₃ × y ≡ ev₂)
  → ¬ po dst x y → ¬ po src x y
¬po[⇐] ¬31 ¬32 ¬po[xy]ᵗ = ¬po[xy]ᵗ ∘ po[⇒] ¬31 ¬32


rfe[⇒] : {x y : Event LabelLIMM} → rfe src x y → rfe dst x y
rfe[⇒] (rf[xy] , ¬po[xy]) =
  let y≢3 = λ{y≡3 → disjoint-f/r _ (ev₃-f , subst EvR y≡3 (×₂-applyʳ (rf-w×r dst-wf) rf[xy]))}
  in rf[xy] , ¬po[⇒] (y≢3 ∘ proj₂) (y≢3 ∘ proj₂) ¬po[xy]

coe[⇒] : {x y : Event LabelLIMM} → coe src x y → coe dst x y
coe[⇒] (co[xy] , ¬po[xy]) =
  let y≢3 = λ{y≡3 → disjoint-f/w _ (ev₃-f , subst EvW y≡3 (×₂-applyʳ (co-w×w dst-wf) co[xy]))}
  in co[xy] , ¬po[⇒] (y≢3 ∘ proj₂) (y≢3 ∘ proj₂) ¬po[xy]

fre[⇒] : {x y : Event LabelLIMM} → fre src x y → fre dst x y
fre[⇒] (fr[xy] , ¬po[xy]) =
  let y≢3 = λ{y≡3 → disjoint-f/w _ (ev₃-f , subst EvW y≡3 (×₂-applyʳ (fr-r×w dst-wf) fr[xy]))}
  in fr[xy] , ¬po[⇒] (y≢3 ∘ proj₂) (y≢3 ∘ proj₂) ¬po[xy]

ghbi[⇒] : {x y : Event LabelLIMM} → GhbiAlt src x y → GhbiAlt dst x y
ghbi[⇒] (ghbi-ord ord[xy]) = ghbi-ord (ord[⇒] ord[xy])
ghbi[⇒] (ghbi-rfe rfe[xy]) = ghbi-rfe (rfe[⇒] rfe[xy])
ghbi[⇒] (ghbi-coe coe[xy]) = ghbi-coe (coe[⇒] coe[xy])
ghbi[⇒] (ghbi-fre fre[xy]) = ghbi-fre (fre[⇒] fre[xy])
