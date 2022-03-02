{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.LIMM using (LabelLIMM)
open import TransformRAR using (RAR-Restricted)


module Proof.Elimination.RAR.Consistent
  (dst : Execution LabelLIMM)
  (dst-ok : RAR-Restricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; flip; id)
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
-- Local imports: Proof Components
open import Proof.Elimination.RAR.Execution dst dst-ok as RAR-Ex
open import Proof.Elimination.RAR.WellFormed dst dst-ok as RAR-Wf
import Proof.Framework LabelLIMM dst dst-wf as Ψ
import Proof.Elimination.Framework dst dst-wf as Δ


-- General Proof Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Elimination Proof Framework
open Δ.Definitions δ
open Δ.WellFormed δ
-- Other
open Ex.Execution
open Ex.WellFormed
open RAR-Ex.Extra
open IsLIMMConsistent
open TransformRAR.Extra dst-ok
open RAR-Restricted dst-ok


dst-consistent = consistent


-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result


-- # Helpers

poʳ-e⇒p : {x : Event LabelLIMM} → x ≢ src-preserved-ev → po src x src-elim-ev → po src x src-preserved-ev
poʳ-e⇒p ¬elim-x po[xe] =
  let lemma = unsplit-poʳ src-wf po[xe] src-transform-pair
  in ⊥⊎-elim ¬elim-x id lemma

poˡ-e⇒p :{y : Event LabelLIMM} → po src src-elim-ev y → po src src-preserved-ev y
poˡ-e⇒p po[ey] = po-trans src-wf (proj₁ src-transform-pair) po[ey]

plˡ-e⇒p : ∀ {y : Event LabelLIMM} → po-loc src src-elim-ev y → po-loc src src-preserved-ev y
plˡ-e⇒p (po[ey] , ey-sloc) = (po-trans src-wf (proj₁ src-transform-pair) po[ey] , trans-same-loc pe-sloc ey-sloc)

plʳ-e⇒p : ∀ {x : Event LabelLIMM} → x ≢ src-preserved-ev → po-loc src x src-elim-ev → po-loc src x src-preserved-ev
plʳ-e⇒p ¬pres-x (po[xe] , xe-sloc) = (poʳ-e⇒p ¬pres-x po[xe] , trans-same-loc xe-sloc (sym-same-loc pe-sloc))

poˡ-p⇒e : {y : Event LabelLIMM} → y ≢ src-elim-ev → po src src-preserved-ev y → po src src-elim-ev y
poˡ-p⇒e ¬elim-y po[py] = 
  let lemma = unsplit-poˡ src-wf pres-¬init po[py] src-transform-pair
  in ⊥⊎-elim (λ{refl → ¬elim-y refl}) id lemma
  where
  pres-¬init : ¬ EvInit src-preserved-ev
  pres-¬init ev-init = disjoint-r/init _ (rₜ⇒r preserved-ev-r , ev-init)

poʳ-p⇒e : {x : Event LabelLIMM} → po src x src-preserved-ev → po src x src-elim-ev
poʳ-p⇒e po[xp] = po-trans src-wf po[xp] (proj₁ src-transform-pair)

¬poˡ-e⇒p : {y : Event LabelLIMM} → y ≢ src-elim-ev → ¬ po src src-elim-ev y → ¬ po src src-preserved-ev y
¬poˡ-e⇒p ¬elim-y ¬po[ey] = ¬po[ey] ∘ poˡ-p⇒e ¬elim-y

¬poʳ-e⇒p : {x : Event LabelLIMM} → ¬ po src x src-elim-ev → ¬ po src x src-preserved-ev
¬poʳ-e⇒p ¬po[xe] = ¬po[xe] ∘ poʳ-p⇒e


freˡ-e⇒p : {y : Event LabelLIMM} → fre src src-elim-ev y → fre src src-preserved-ev y
freˡ-e⇒p (fr[ey] , ¬po[ey]) =
  let ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
  in frˡ-e⇒p fr[ey] , ¬poˡ-e⇒p ¬y-elim ¬po[ey]

rfeʳ-e⇒p : {x : Event LabelLIMM} → rfe src x src-elim-ev → rfe src x src-preserved-ev
rfeʳ-e⇒p (rf[xe] , ¬po[xe]) = rfʳ-e⇒p rf[xe] , ¬poʳ-e⇒p ¬po[xe]

pres-r : EvR src-preserved-ev
pres-r = rₜ⇒r preserved-ev-r

pres-rw : EvRW src-preserved-ev
pres-rw = rₜ⇒rw preserved-ev-r

¬init-pres : {x : Event LabelLIMM} → EvInit x → x ≢ src-preserved-ev
¬init-pres ev-init refl = disjoint-r/init _ (pres-r , ev-init)

¬f-pres : {x : Event LabelLIMM} → EvF x → x ≢ src-preserved-ev
¬f-pres x-f refl = disjoint-f/r _ (x-f , pres-r)

¬w-pres : {x : Event LabelLIMM} → EvW x → x ≢ src-preserved-ev
¬w-pres x-w refl = disjoint-r/w _ (pres-r , x-w)


-- # Coherence

CohDetour : Rel (Event LabelLIMM) ℓzero
CohDetour x y = Coh src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)

cohˡ-e⇒p : {y : Event LabelLIMM} → Coh src src-elim-ev y → Coh src src-preserved-ev y
cohˡ-e⇒p (coh-po-loc pl[ey]) = coh-po-loc (plˡ-e⇒p pl[ey])
cohˡ-e⇒p (coh-fr fr[ey])     = coh-fr (frˡ-e⇒p fr[ey])
cohˡ-e⇒p (coh-rf rf[ey])     = ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , ×₂-applyˡ (rf-w×r src-wf) rf[ey]))
cohˡ-e⇒p (coh-co co[ey])     = ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , ×₂-applyˡ (co-w×w src-wf) co[ey]))

cohʳ-e⇒p : {x : Event LabelLIMM} → x ≢ src-preserved-ev → Coh src x src-elim-ev → Coh src x src-preserved-ev
cohʳ-e⇒p ¬pres-x (coh-po-loc pl[xe]) = coh-po-loc (plʳ-e⇒p ¬pres-x pl[xe])
cohʳ-e⇒p ¬pres-x (coh-rf rf[xe]) = coh-rf (rfʳ-e⇒p rf[xe])
cohʳ-e⇒p ¬pres-x (coh-fr fr[xe]) = ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , ×₂-applyʳ (fr-r×w src-wf) fr[xe]))
cohʳ-e⇒p ¬pres-x (coh-co co[xe]) = ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , ×₂-applyʳ (co-w×w src-wf) co[xe]))


coh-detour : ∀ {x : Event LabelLIMM} → TransClosure (Coh src) x x → ∃[ z ] TransClosure CohDetour z z
coh-detour coh⁺[xx] with divert-cycle coh⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
coh-detour coh⁺[xx] | inj₁ (cycle₁ coh[ee]) = ⊥-elim (coh-irreflexive src-wf refl coh[ee])
coh-detour coh⁺[xx] | inj₁ (cycle₂ {y} ¬elim-y coh[ey] coh[ye]) with ev-eq-dec y src-preserved-ev
... | yes refl    = ⊥-elim (coh-irreflexive src-wf refl (cohˡ-e⇒p coh[ey])) -- x ≡ p
... | no ¬pres-y = _ , (cohˡ-e⇒p coh[ey] , ¬elim-pres-src , ¬elim-y) ∷ [ cohʳ-e⇒p ¬pres-y coh[ye] , ¬elim-y , ¬elim-pres-src ]
coh-detour coh⁺[xx] | inj₁ (cycleₙ {x} {y} coh[ex] cohd⁺[xy] coh[ye]) with ev-eq-dec y src-preserved-ev
... | yes refl    = _ , (cohˡ-e⇒p coh[ex] , ¬elim-pres-src , ⁺-lift-predˡ (proj₁ ∘ proj₂) cohd⁺[xy]) ∷ cohd⁺[xy] -- y ≡ p
... | no ¬pres-y =
  let ¬elim-y = ⁺-lift-predʳ (proj₂ ∘ proj₂) cohd⁺[xy]
      ¬elim-x = ⁺-lift-predˡ (proj₁ ∘ proj₂) cohd⁺[xy]
  in _ , ((cohʳ-e⇒p ¬pres-y coh[ye] , ¬elim-y , ¬elim-pres-src) ∷ (cohˡ-e⇒p coh[ex] , ¬elim-pres-src , ¬elim-x) ∷ cohd⁺[xy])
coh-detour coh⁺[xx] | inj₂ cohd⁺[xx] = _ , cohd⁺[xx]

frˡ∈src : {x y : Event LabelLIMM} → fr src x y → x ∈ events src
frˡ∈src (rf⁻¹[xz] ⨾[ _ ]⨾ co[zy]) = rfʳ∈src rf⁻¹[xz]


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
  coh[⇒] x∈src y∈src (coh-fr fr[xy] , ¬elim-x , ¬elim-y) = coh-fr (fr[⇒] ¬elim-x x∈src y∈src fr[xy])
  coh[⇒] x∈src y∈src (coh-co co[xy] , ¬elim-x , ¬elim-y) = coh-co (co[⇒] ¬elim-x ¬elim-y x∈src y∈src co[xy])

  cohdˡ∈src : CohDetour ˡ∈src
  cohdˡ∈src (coh[xy] , _ , _) = cohˡ∈ex src-wf coh[xy]



-- # Atomicity

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
      ¬elim-x = λ{refl → disjoint-rₜ _ (elim-rₜ , ×₂-applyˡ (rmw-r×w src-wf) rmw[xy])}
      ¬elim-y = elim-¬w (src-coʳ-w (proj₁ coe[zy]))
      ¬elim-z = elim-¬w (src-coˡ-w (proj₁ coe[zy]))
  in
  ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] ¬elim-x x∈src z∈src fre[xz] ⨾[ ev[⇒] z∈src ]⨾ coe[⇒] ¬elim-z ¬elim-y z∈src y∈src coe[zy]
    )

ordʳ-e⇒p : ∀ {x : Event LabelLIMM} → OrdAlt src x src-elim-ev → OrdAlt src x src-preserved-ev
ordʳ-e⇒p (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , _))) =
  let po[xp] = poʳ-e⇒p (¬init-pres x-init) po[xe]
  in ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xp] ⨾[ _ ]⨾ (refl , pres-rw))
-- RM
ordʳ-e⇒p (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , e-m))) =
  let po[zp] = poʳ-e⇒p (¬f-pres (f₌⇒f z-f)) po[ze]
  in ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zp] ⨾[ _ ]⨾ (refl , pres-rw))
-- SC
ordʳ-e⇒p (ord-sc ((refl , x-m) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , e-m))) =
  let po[zp] = poʳ-e⇒p (¬f-pres (f₌⇒f z-f)) po[ze]
  in ord-sc ((refl , x-m) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zp] ⨾[ _ ]⨾ (refl , pres-rw))
ordʳ-e⇒p {x} (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬x-pres = ¬w-pres (wₜ⇒w (rmwʳ-w src-wf x∈rmwʳ))
      po[xp] = poʳ-e⇒p ¬x-pres po[xe]
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xp] ⨾[ _ ]⨾ (refl , pres-rw))
-- atomic read
ordʳ-e⇒p {x} (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬x-pres = λ{refl → disjoint-rₜ _ (preserved-ev-r , x-rₜ)}
      po[xp] = poʳ-e⇒p ¬x-pres po[xe]
  in ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xp] ⨾[ _ ]⨾ (refl , pres-rw))
-- impossible cases
-- WW
ordʳ-e⇒p (ord-ww ((refl , x-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , e-w))) =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , e-w))
-- rmwˡ
ordʳ-e⇒p (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e∈rmwˡ))) =
  ⊥-elim (disjoint-rₜ _ (elim-rₜ , rmwˡ-r src-wf e∈rmwˡ))
-- atomic write
ordʳ-e⇒p (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-wₜ))) =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , wₜ⇒w e-wₜ))


ordˡ-e⇒p : ∀ {y : Event LabelLIMM} → OrdAlt src src-elim-ev y → OrdAlt src src-preserved-ev y
ordˡ-e⇒p (ord-rm ((refl , e-r) ⨾[ _ ]⨾ po[ez] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-m))) =
  ord-rm ((refl , pres-r) ⨾[ _ ]⨾ poˡ-e⇒p po[ez] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-m))
ordˡ-e⇒p (ord-sc ((refl , e-m) ⨾[ _ ]⨾ po[ez] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-m))) =
  ord-sc ((refl , pres-rw) ⨾[ _ ]⨾ poˡ-e⇒p po[ez] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-m))
ordˡ-e⇒p (ord-rmw-dom ((refl , e-rw) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y∈rmwˡ))) =
  ord-rmw-dom ((refl , pres-rw) ⨾[ _ ]⨾ poˡ-e⇒p po[ey] ⨾[ _ ]⨾ (refl , y∈rmwˡ))
ordˡ-e⇒p (ord-w ((refl , e-rw) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-wₜ))) =
  ord-w ((refl , pres-rw) ⨾[ _ ]⨾ poˡ-e⇒p po[ey] ⨾[ _ ]⨾ (refl , y-wₜ))
-- impossible cases
ordˡ-e⇒p (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , _))) =
  ⊥-elim (disjoint-r/init _ (rₜ⇒r elim-rₜ , x-init))
ordˡ-e⇒p (ord-ww ((refl , e-w) ⨾[ _ ]⨾ po[ez] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-w))) =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , e-w))
ordˡ-e⇒p (ord-rmw-codom ((refl , e∈rmwʳ) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-rw))) =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , wₜ⇒w (rmwʳ-w src-wf e∈rmwʳ)))
ordˡ-e⇒p (ord-r ((refl , e-rₜ) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-rw))) =
  ⊥-elim (disjoint-rₜ _ (elim-rₜ , e-rₜ))


ghbiˡ-e⇒p : {y : Event LabelLIMM} → GhbiAlt src src-elim-ev y → GhbiAlt src src-preserved-ev y
ghbiˡ-e⇒p (ghbi-ord ord[ey]) = ghbi-ord (ordˡ-e⇒p ord[ey])
ghbiˡ-e⇒p (ghbi-fre fre[ey]) = ghbi-fre (freˡ-e⇒p fre[ey])
ghbiˡ-e⇒p (ghbi-rfe rfe[ey]) = ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , ×₂-applyˡ (rfe-w×r src-wf) rfe[ey]))
ghbiˡ-e⇒p (ghbi-coe coe[ey]) = ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , ×₂-applyˡ (coe-w×w src-wf) coe[ey]))

ghbiʳ-e⇒p : {x : Event LabelLIMM} → GhbiAlt src x src-elim-ev → GhbiAlt src x src-preserved-ev
ghbiʳ-e⇒p (ghbi-ord ord[xe]) = ghbi-ord (ordʳ-e⇒p ord[xe])
ghbiʳ-e⇒p (ghbi-rfe rfe[xe]) = ghbi-rfe (rfeʳ-e⇒p rfe[xe])
ghbiʳ-e⇒p (ghbi-coe coe[xe]) = ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , ×₂-applyʳ (coe-w×w src-wf) coe[xe]))
ghbiʳ-e⇒p (ghbi-fre fre[xe]) = ⊥-elim (disjoint-r/w _ (rₜ⇒r elim-rₜ , ×₂-applyʳ (fre-r×w src-wf) fre[xe]))

GhbiAltDetour : Rel (Event LabelLIMM) ℓzero
GhbiAltDetour x y = GhbiAlt src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)
  
ghb-detour : ∀ {x : Event LabelLIMM} → TransClosure (GhbiAlt src) x x → ∃[ z ] TransClosure GhbiAltDetour z z
ghb-detour {x} ghbi⁺[xx] with divert-cycle ghbi⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
... | inj₁ (cycle₁ ghbi[xx]) =
  ⊥-elim (¬ghbi-cycle₁ src-wf ghbi[xx])
... | inj₁ (cycle₂ ¬elim-x ghbi[ex] ghbi[xe]) =
  ⊥-elim (¬ghbi-cycle₂ src-wf src-ax-coherence ghbi[ex] ghbi[xe])
... | inj₁ (cycleₙ ghbi[ex] ghbid⁺[xy] ghbi[ye]) =
  let ¬elim-x = ⁺-lift-predˡ (proj₁ ∘ proj₂) ghbid⁺[xy]
      ¬elim-y = ⁺-lift-predʳ (proj₂ ∘ proj₂) ghbid⁺[xy]
  in _ , (ghbiʳ-e⇒p ghbi[ye] , ¬elim-y , ¬elim-pres-src) ∷ (ghbiˡ-e⇒p ghbi[ex] , ¬elim-pres-src , ¬elim-x) ∷ ghbid⁺[xy]
... | inj₂ ghbid⁺[xx] = (_ , ghbid⁺[xx])

ghbi[⇒] : Rel[⇒] GhbiAltDetour (GhbiAlt dst)
ghbi[⇒] x∈src y∈src (ghbi-ord ord[xy] , ¬elim-x , ¬elim-y) = ghbi-ord (ord[⇒] ¬elim-x ¬elim-y x∈src y∈src ord[xy])
ghbi[⇒] x∈src y∈src (ghbi-rfe rfe[xy] , ¬elim-x , ¬elim-y) = ghbi-rfe (rfe[⇒] ¬elim-x ¬elim-y x∈src y∈src rfe[xy])
ghbi[⇒] x∈src y∈src (ghbi-coe coe[xy] , ¬elim-x , ¬elim-y) = ghbi-coe (coe[⇒] ¬elim-x ¬elim-y x∈src y∈src coe[xy])
ghbi[⇒] x∈src y∈src (ghbi-fre fre[xy] , ¬elim-x , ¬elim-y) = ghbi-fre (fre[⇒] ¬elim-x x∈src y∈src fre[xy])

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


src-consistent : IsLIMMConsistent src
src-consistent =
  record
    { ax-coherence  = src-ax-coherence
    ; ax-atomicity  = src-ax-atomicity
    ; ax-global-ord = src-ax-global-ord
    }
