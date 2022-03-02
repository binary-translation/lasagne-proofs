{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.LIMM using (LabelLIMM)
open import TransformWAW using (WAW-Restricted)


module Proof.Elimination.WAW.Consistent
  (dst : Execution LabelLIMM)
  (dst-ok : WAW-Restricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; _∘₂_; flip; id)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; Irreflexive; tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_]; _++_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architecture Definitions
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.LIMM as LIMM
open import Arch.LIMM.Detour
-- Local imports: Theorem Specification
open import TransformWAW
-- Local imports: Proof Components
open import Proof.Elimination.WAW.Execution dst dst-ok as WAW-Ex
open import Proof.Elimination.WAW.WellFormed dst dst-ok as WAW-Wf
import Proof.Framework LabelLIMM dst dst-wf as Ψ
import Proof.Elimination.Framework dst dst-wf as Δ


-- General Proof Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Elimination Proof Framework
open Δ.Definitions δ
open Δ.WellFormed δ
-- Other
open WAW-Restricted dst-ok
open TransformWAW.Extra dst-ok
open Ex.Execution
open Ex.WellFormed
open WAW-Ex.Extra
open IsLIMMConsistent


dst-consistent = consistent


-- # Coherence

CohDetour : Rel (Event LabelLIMM) ℓzero
CohDetour x y = Coh src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)

¬elim-init : ¬ EvInit src-elim-ev
¬elim-init e-init = disjoint-wₙ/init _ (wₙₜ⇒wₙ elim-wₙₜ , e-init)

poˡ-e⇒p : {y : Event LabelLIMM} → y ≢ src-preserved-ev → po src src-elim-ev y → po src src-preserved-ev y
poˡ-e⇒p ¬y-pres po[ey] =
  let lemma = unsplit-poˡ src-wf ¬elim-init po[ey] src-transform-pair
  in ⊥⊎-elim (≢-sym ¬y-pres) id lemma

poʳ-e⇒p : {x : Event LabelLIMM} → po src x src-elim-ev → po src x src-preserved-ev
poʳ-e⇒p po[xe] = po-trans src-wf po[xe] (proj₁ src-transform-pair)


plˡ-e⇒p : {y : Event LabelLIMM} → y ≢ src-preserved-ev → po-loc src src-elim-ev y → po-loc src src-preserved-ev y
plˡ-e⇒p ¬y-pres (po[ey] , ey-sloc) = poˡ-e⇒p ¬y-pres po[ey] , trans-same-loc pe-sloc ey-sloc

plʳ-e⇒p : {x : Event LabelLIMM} → po-loc src x src-elim-ev → po-loc src x src-preserved-ev
plʳ-e⇒p (po[xe] , xe-sloc) = poʳ-e⇒p po[xe] , trans-same-loc xe-sloc (sym-same-loc pe-sloc)


¬rfˡ-e : {y : Event LabelLIMM} → ¬ rf src src-elim-ev y
¬rfˡ-e (_ , _ , rf[ey] , p , refl) with ev[$⇒]eq elim∈ex (rfˡ∈ex dst-wf rf[ey]) p
... | refl = disjoint-w/skip _ (×₂-applyˡ (rf-w×r dst-wf) rf[ey] , elim-ev-skip)


cohˡ-e⇒p : {y : Event LabelLIMM} → y ≢ src-preserved-ev → Coh src src-elim-ev y → Coh src src-preserved-ev y
cohˡ-e⇒p ¬y-pres (coh-po-loc pl[ey]) = coh-po-loc (plˡ-e⇒p ¬y-pres pl[ey])
cohˡ-e⇒p ¬y-pres (coh-co co[ey])     = coh-co (coˡ-e⇒p ¬y-pres co[ey])
-- impossible cases
cohˡ-e⇒p ¬y-pres (coh-rf rf[ey])     = ⊥-elim (¬rfˡ-e rf[ey])
cohˡ-e⇒p ¬y-pres (coh-fr fr[ey])     = ⊥-elim (disjoint-r/w _ (×₂-applyˡ (fr-r×w src-wf) fr[ey] , src-elim-w))


cohʳ-e⇒p : {x : Event LabelLIMM} → Coh src x src-elim-ev → Coh src x src-preserved-ev
cohʳ-e⇒p (coh-po-loc pl[xe]) = coh-po-loc (plʳ-e⇒p pl[xe])
cohʳ-e⇒p (coh-fr fr[xe])     = coh-fr (frʳ-e⇒p fr[xe])
cohʳ-e⇒p (coh-co co[xe])     = coh-co (coʳ-e⇒p co[xe])
-- impossible cases
cohʳ-e⇒p (coh-rf rf[xe])     = ⊥-elim (disjoint-r/w _ (×₂-applyʳ (rf-w×r src-wf) rf[xe] , src-elim-w))


¬pres-elim : src-preserved-ev ≢ src-elim-ev
¬pres-elim p≡e = po-irreflexive src-wf (≡-sym p≡e) (proj₁ src-transform-pair)


coh-detour : ∀ {x : Event LabelLIMM} → TransClosure (Coh src) x x → ∃[ z ] TransClosure CohDetour z z
coh-detour coh⁺[xx] with divert-cycle coh⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
coh-detour coh⁺[xx] | inj₁ (cycle₁ coh[ee]) = ⊥-elim (coh-irreflexive src-wf refl coh[ee])
coh-detour coh⁺[xx] | inj₁ (cycle₂ {y} ¬y-elim coh[ey] coh[ye]) with ev-eq-dec y src-preserved-ev
... | yes refl   = ⊥-elim (coh-irreflexive src-wf refl (cohʳ-e⇒p coh[ye])) -- y ≡ p
... | no ¬y-pres = _ , ((cohˡ-e⇒p ¬y-pres coh[ey] , ¬pres-elim , ¬y-elim) ∷ [ cohʳ-e⇒p coh[ye] , ¬y-elim , ¬pres-elim ])
coh-detour coh⁺[xx] | inj₁ (cycleₙ {x} {y} coh[ex] cohd⁺[xy] coh[ye]) with ev-eq-dec x src-preserved-ev
... | yes refl   =
  let coh[yp] = cohʳ-e⇒p coh[ye]
      ¬y-elim = ⁺-lift-predʳ (proj₂ ∘ proj₂) cohd⁺[xy]
  in _ , ((coh[yp] , ¬y-elim , ¬pres-elim) ∷ cohd⁺[xy])
... | no ¬x-pres =
  let ¬x-elim = ⁺-lift-predˡ (proj₁ ∘ proj₂) cohd⁺[xy]
      ¬y-elim = ⁺-lift-predʳ (proj₂ ∘ proj₂) cohd⁺[xy]
  in _ , ((cohʳ-e⇒p coh[ye] , ¬y-elim , ¬pres-elim) ∷ (cohˡ-e⇒p ¬x-pres coh[ex] , ¬pres-elim , ¬x-elim) ∷ cohd⁺[xy])
coh-detour coh⁺[xx] | inj₂ cohd⁺[xx] = _ , cohd⁺[xx]


fr[⇒] : CRel[⇒] (fr src) (fr dst)
fr[⇒] ¬x-elim ¬y-elim x∈src y∈src (rf⁻¹[xz] ⨾[ _ ]⨾ co[zy]) =
  let z∈src = coˡ∈src co[zy]
      ¬z-elim = λ{refl → ¬rfˡ-e rf⁻¹[xz]}
  in rf[⇒] ¬z-elim ¬x-elim z∈src x∈src rf⁻¹[xz] ⨾[ _ ]⨾ co[⇒] ¬z-elim ¬y-elim z∈src y∈src co[zy]

fre[⇒] : CRel[⇒] (fre src) (fre dst)
fre[⇒] ¬x-elim ¬y-elim x∈src y∈src (fr[xy] , ¬po[xy]) =
  fr[⇒] ¬x-elim ¬y-elim x∈src y∈src fr[xy] , ¬po[⇒] x∈src y∈src ¬po[xy]


src-ax-coherence  : Acyclic _≡_ ( Coh src )
src-ax-coherence refl coh⁺[xx] =
  let (z , cohd⁺[zz]) = coh-detour coh⁺[xx]
      z∈src = ⁺-lift-predˡ cohdˡ∈src cohd⁺[zz]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ cohdˡ∈src coh[⇒] z∈src z∈src cohd⁺[zz])
  where
  coh[⇒] : Rel[⇒] CohDetour (Coh dst)
  coh[⇒] x∈src y∈src (coh-po-loc pl[xy] , ¬elim-x , ¬elim-y) =
    coh-po-loc (po-loc[⇒] ¬elim-x ¬elim-y x∈src y∈src pl[xy])
  coh[⇒] x∈src y∈src (coh-rf rf[xy] , ¬elim-x , ¬elim-y) = coh-rf (rf[⇒] ¬elim-x ¬elim-y x∈src y∈src rf[xy])
  coh[⇒] x∈src y∈src (coh-fr fr[xy] , ¬elim-x , ¬elim-y) = coh-fr (fr[⇒] ¬elim-x ¬elim-y x∈src y∈src fr[xy])
  coh[⇒] x∈src y∈src (coh-co co[xy] , ¬elim-x , ¬elim-y) = coh-co (co[⇒] ¬elim-x ¬elim-y x∈src y∈src co[xy])

  cohdˡ∈src : CohDetour ˡ∈src
  cohdˡ∈src (coh[xy] , _ , _) = cohˡ∈ex src-wf coh[xy]


-- # Atomicity

poˡ-p⇒e : {y : Event LabelLIMM} → po src src-preserved-ev y → po src src-elim-ev y
poˡ-p⇒e = po-trans src-wf (proj₁ src-transform-pair)

poʳ-p⇒e : {x : Event LabelLIMM} → x ≢ src-elim-ev → po src x src-preserved-ev → po src x src-elim-ev
poʳ-p⇒e ¬x-elim po[xp] = ⊥⊎-elim ¬x-elim id (unsplit-poʳ src-wf po[xp] src-transform-pair)

¬poʳ-e⇒p : {x : Event LabelLIMM} → x ≢ src-elim-ev → ¬ po src x src-elim-ev → ¬ po src x src-preserved-ev
¬poʳ-e⇒p = contrapositive ∘ poʳ-p⇒e

¬poˡ-e⇒p : {y : Event LabelLIMM} → ¬ po src src-elim-ev y → ¬ po src src-preserved-ev y
¬poˡ-e⇒p = contrapositive poˡ-p⇒e

freʳ-e⇒p : {x : Event LabelLIMM} → fre src x src-elim-ev → fre src x src-preserved-ev
freʳ-e⇒p (fr[xe] , ¬po[xe]) =
  let ¬x-elim = λ{refl → fr-irreflexive src-wf refl fr[xe]}
  in frʳ-e⇒p fr[xe] , ¬poʳ-e⇒p ¬x-elim ¬po[xe]

coeˡ-e⇒p : {y : Event LabelLIMM} → y ≢ src-preserved-ev → coe src src-elim-ev y → coe src src-preserved-ev y
coeˡ-e⇒p ¬y-pres (co[xe] , ¬po[xe]) = coˡ-e⇒p ¬y-pres co[xe] , ¬poˡ-e⇒p ¬po[xe]

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy]))
  with ev-eq-dec z src-elim-ev
... | yes refl =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      ¬x-elim = λ{refl → disjoint-r/w _ (rₜ⇒r (rmwˡ-r src-wf (take-dom (rmw src) rmw[xy])) , src-elim-w)}
      ¬y-elim = λ{refl → disjoint-wₜ _ (wₙₜ⇒wₜ elim-wₙₜ , rmwʳ-w src-wf (take-codom (rmw src) rmw[xy]))}
      ¬y-pres = λ{refl → disjoint-wₜ _ (src-preserved-wᵣ , rmwʳ-w src-wf (take-codom (rmw src) rmw[xy]))}
      fre[xp] = freʳ-e⇒p fre[xz]
      coe[py] = coeˡ-e⇒p ¬y-pres coe[zy]
  in
  ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] ¬x-elim ¬pres-elim x∈src preserved∈src fre[xp] ⨾[ _ ]⨾ coe[⇒] ¬pres-elim ¬y-elim preserved∈src y∈src coe[py]
    )
... | no ¬z-elim =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
      ¬x-elim = λ{refl → disjoint-r/w _ (rₜ⇒r (rmwˡ-r src-wf (take-dom (rmw src) rmw[xy])) , src-elim-w)}
      ¬y-elim = λ{refl → disjoint-wₜ _ (wₙₜ⇒wₜ elim-wₙₜ , rmwʳ-w src-wf (take-codom (rmw src) rmw[xy]))}
  in
  ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] ¬x-elim ¬z-elim x∈src z∈src fre[xz] ⨾[ _ ]⨾ coe[⇒] ¬z-elim ¬y-elim z∈src y∈src coe[zy]
    )
    

-- # Global Order

GhbiAltDetour : Rel (Event LabelLIMM) ℓzero
GhbiAltDetour x y = GhbiAlt src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)


coeʳ-e⇒p : {x : Event LabelLIMM} → coe src x src-elim-ev → coe src x src-preserved-ev
coeʳ-e⇒p (co[xe] , ¬po[xe]) =
  let ¬x-elim = λ{refl → co-irreflexive src-wf refl co[xe]}
  in (coʳ-e⇒p co[xe] , ¬poʳ-e⇒p ¬x-elim ¬po[xe])


ordfˡ-e⇒p : {P₁ P₂ : Pred (Event LabelLIMM) ℓzero} {f : F-mode}
  → {y : Event LabelLIMM}
  → ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ f ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) src-elim-ev y
  → P₁ src-preserved-ev
  → ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ f ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) src-preserved-ev y
ordfˡ-e⇒p ((refl , e-p₁) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-p₁)) p-p₁ =
  let ¬y-pres = λ{refl → disjoint-f/w _ (f₌⇒f z-f , src-preserved-w)}
  in (refl , p-p₁) ⨾[ _ ]⨾ poˡ-e⇒p ¬y-pres po[ey] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-p₁)


ordˡ-e⇒p : {y : Event LabelLIMM} → OrdAlt src src-elim-ev y → OrdAlt src src-preserved-ev y
ordˡ-e⇒p (ord-ww ww[ey]) = ord-ww (ordfˡ-e⇒p ww[ey] src-preserved-w)
ordˡ-e⇒p (ord-sc sc[ey]) = ord-sc (ordfˡ-e⇒p sc[ey] (w⇒rw src-preserved-w))
ordˡ-e⇒p (ord-rmw-dom ((refl , e-rw) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y∈rmwˡ))) =
  let ¬y-pres = λ{refl → disjoint-r/w _ (rₜ⇒r (rmwˡ-r src-wf y∈rmwˡ) , src-preserved-w)}
  in ord-rmw-dom ((refl , w⇒rw src-preserved-w) ⨾[ _ ]⨾ poˡ-e⇒p ¬y-pres po[ey] ⨾[ _ ]⨾ (refl , y∈rmwˡ))
ordˡ-e⇒p (ord-w ((refl , e-rw) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-wₜ))) =
  let ¬pres-y = λ{refl → disjoint-wₜ _ (src-preserved-wᵣ , y-wₜ)}
  in ord-w ((refl , w⇒rw src-preserved-w) ⨾[ _ ]⨾ poˡ-e⇒p ¬pres-y po[ey] ⨾[ _ ]⨾ (refl , y-wₜ))
-- impossible cases
ordˡ-e⇒p (ord-init ((refl , e-init) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , _))) =
  ⊥-elim (disjoint-wₙ/init _ (wₙₜ⇒wₙ elim-wₙₜ , e-init))
ordˡ-e⇒p (ord-rm rm[ey]) = ⊥-elim (disjoint-r/w _ (ord-predˡ src rm[ey] , src-elim-w))
ordˡ-e⇒p (ord-rmw-codom ((refl , e∈rmwʳ) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-rw))) =
  ⊥-elim (disjoint-wₜ _ (wₙₜ⇒wₜ elim-wₙₜ , rmwʳ-w src-wf e∈rmwʳ))
ordˡ-e⇒p (ord-r ((refl , e-rₜ) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-rw))) =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r e-rₜ , src-elim-w))


ordfʳ-e⇒p : {P₁ P₂ : Pred (Event LabelLIMM) ℓzero} {f : F-mode}
  → {x : Event LabelLIMM}
  → ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ f ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x src-elim-ev
  → P₂ src-preserved-ev
  → ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ f ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x src-preserved-ev
ordfʳ-e⇒p ((refl , x-p₁) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , y-p₁)) p-p₂ =
  (refl , x-p₁) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ poʳ-e⇒p po[ze] ⨾[ _ ]⨾ (refl , p-p₂)
  

ordʳ-e⇒p : {x : Event LabelLIMM} → OrdAlt src x src-elim-ev → OrdAlt src x src-preserved-ev
ordʳ-e⇒p (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , _))) =
  ord-init ((refl , x-init) ⨾[ _ ]⨾ poʳ-e⇒p po[xe] ⨾[ _ ]⨾ (refl , w⇒rw src-preserved-w))
ordʳ-e⇒p (ord-rm rm[xe]) = ord-rm (ordfʳ-e⇒p rm[xe] (w⇒rw src-preserved-w))
ordʳ-e⇒p (ord-ww ww[xe]) = ord-ww (ordfʳ-e⇒p ww[xe] src-preserved-w)
ordʳ-e⇒p (ord-sc sc[xe]) = ord-sc (ordfʳ-e⇒p sc[xe] (w⇒rw src-preserved-w))
ordʳ-e⇒p (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ poʳ-e⇒p po[xe] ⨾[ _ ]⨾ (refl , w⇒rw src-preserved-w))
ordʳ-e⇒p (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ poʳ-e⇒p po[xe] ⨾[ _ ]⨾ (refl , w⇒rw src-preserved-w))
-- impossible cases
ordʳ-e⇒p (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e∈rmwˡ))) =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r (rmwˡ-r src-wf e∈rmwˡ) , src-elim-w))
ordʳ-e⇒p (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-wₜ))) =
  ⊥-elim (disjoint-wₜ _ (wₙₜ⇒wₜ elim-wₙₜ , e-wₜ))


ghbiˡ-e⇒p : {y : Event LabelLIMM} → y ≢ src-preserved-ev → GhbiAlt src src-elim-ev y → GhbiAlt src src-preserved-ev y
ghbiˡ-e⇒p ¬y-pres (ghbi-ord ord[ey]) = ghbi-ord (ordˡ-e⇒p ord[ey])
ghbiˡ-e⇒p ¬y-pres (ghbi-coe coe[ey]) = ghbi-coe (coeˡ-e⇒p ¬y-pres coe[ey])
-- impossible cases
ghbiˡ-e⇒p ¬y-pres (ghbi-rfe rfe[ey]) = ⊥-elim (¬rfˡ-e (proj₁ rfe[ey]))
ghbiˡ-e⇒p ¬y-pres (ghbi-fre fre[ey]) = ⊥-elim (disjoint-r/w _ (×₂-applyˡ (fre-r×w src-wf) fre[ey] , src-elim-w))


ghbiʳ-e⇒p : {x : Event LabelLIMM} → GhbiAlt src x src-elim-ev → GhbiAlt src x src-preserved-ev
ghbiʳ-e⇒p (ghbi-ord ord[xe]) = ghbi-ord (ordʳ-e⇒p ord[xe])
ghbiʳ-e⇒p (ghbi-coe coe[xe]) = ghbi-coe (coeʳ-e⇒p coe[xe])
ghbiʳ-e⇒p (ghbi-fre fre[xe]) = ghbi-fre (freʳ-e⇒p fre[xe])
-- impossible cases
ghbiʳ-e⇒p (ghbi-rfe rfe[xe]) = ⊥-elim (disjoint-r/w _ (×₂-applyʳ (rfe-w×r src-wf) rfe[xe] , src-elim-w))


ghb-detour : ∀ {x : Event LabelLIMM} → TransClosure (GhbiAlt src) x x → ∃[ z ] TransClosure GhbiAltDetour z z
ghb-detour {x}  ghbi⁺[xx] with divert-cycle ghbi⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
... | inj₁ (cycle₁ ghbi[xx]) = ⊥-elim (GhbiAlt-irreflexive src-wf refl ghbi[xx])
... | inj₁ (cycle₂ {x} ¬x-elim ghbi[ex] ghbi[xe]) =
  let ¬x-pres = λ{refl → GhbiAlt-irreflexive src-wf refl (ghbiʳ-e⇒p ghbi[xe])}
  in _ , ((ghbiˡ-e⇒p ¬x-pres ghbi[ex] , ¬pres-elim , ¬x-elim) ∷ [ ghbiʳ-e⇒p ghbi[xe] , ¬x-elim , ¬pres-elim ])
... | inj₂ ghbid⁺[xx] = (_ , ghbid⁺[xx])
... | inj₁ (cycleₙ {x} ghbi[ex] ghbid⁺[xy] ghbi[ye])
  with ev-eq-dec x src-preserved-ev
... | yes refl =
  let ¬x-elim = ⁺-lift-predˡ (proj₁ ∘ proj₂) ghbid⁺[xy]
      ¬y-elim = ⁺-lift-predʳ (proj₂ ∘ proj₂) ghbid⁺[xy]
  in _ , (ghbiʳ-e⇒p ghbi[ye] , ¬y-elim , ¬pres-elim) ∷ ghbid⁺[xy]
... | no ¬x-pres =
  let ¬x-elim = ⁺-lift-predˡ (proj₁ ∘ proj₂) ghbid⁺[xy]
      ¬y-elim = ⁺-lift-predʳ (proj₂ ∘ proj₂) ghbid⁺[xy]
  in _ , ((ghbiʳ-e⇒p ghbi[ye] , ¬y-elim , ¬pres-elim) ∷ (ghbiˡ-e⇒p ¬x-pres ghbi[ex] , ¬pres-elim , ¬x-elim) ∷ ghbid⁺[xy])

ghbi[⇒] : Rel[⇒] GhbiAltDetour (GhbiAlt dst)
ghbi[⇒] x∈src y∈src (ghbi-ord ord[xy] , ¬elim-x , ¬elim-y) = ghbi-ord (ord[⇒] ¬elim-x ¬elim-y x∈src y∈src ord[xy])
ghbi[⇒] x∈src y∈src (ghbi-rfe rfe[xy] , ¬elim-x , ¬elim-y) = ghbi-rfe (rfe[⇒] ¬elim-x ¬elim-y x∈src y∈src rfe[xy])
ghbi[⇒] x∈src y∈src (ghbi-coe coe[xy] , ¬elim-x , ¬elim-y) = ghbi-coe (coe[⇒] ¬elim-x ¬elim-y x∈src y∈src coe[xy])
ghbi[⇒] x∈src y∈src (ghbi-fre fre[xy] , ¬elim-x , ¬elim-y) = ghbi-fre (fre[⇒] ¬elim-x ¬elim-y x∈src y∈src fre[xy])


ghbidˡ∈src : {x y : Event LabelLIMM} → GhbiAltDetour x y → x ∈ events src
ghbidˡ∈src (ghbi-ord ord[xy] , _ , _) = OrdAltˡ∈ex src-wf ord[xy]
ghbidˡ∈src (ghbi-rfe rfe[xy] , _ , _) = rfˡ∈ex src-wf (proj₁ rfe[xy])
ghbidˡ∈src (ghbi-coe coe[xy] , _ , _) = coˡ∈ex src-wf (proj₁ coe[xy])
ghbidˡ∈src (ghbi-fre fre[xy] , _ , _) = frˡ∈ex src-wf (proj₁ fre[xy])


src-ax-global-ord : Irreflexive _≡_ (ghb src)
src-ax-global-ord refl ghb[xx] =
  -- First, find a detour that only goes between R/W events. Then find a detour that does /not/ go
  -- through the eliminated event.
  let (y , ghbd[yy]) = ghb-detour (proj₂ (detour src-wf ghb[xx]))
      y∈src = ⁺-lift-predˡ (GhbiAltˡ∈ex src-wf ∘ proj₁) ghbd[yy]
  in ax-global-ord dst-consistent refl (GhbiAlt⁺⇒Ghbi⁺ (⁺[⇒]ˡ ghbidˡ∈src ghbi[⇒] y∈src y∈src ghbd[yy]))


-- # Consistent

src-consistent : IsLIMMConsistent src
src-consistent =
  record
    { ax-coherence  = src-ax-coherence
    ; ax-atomicity  = src-ax-atomicity
    ; ax-global-ord = src-ax-global-ord
    }
