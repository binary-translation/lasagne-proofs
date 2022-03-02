{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.LIMM using (LabelLIMM)
open import TransformFRAW using (FRAW-Restricted)


-- | Fence-Read-After-Write elimination consistency proof.
--
-- See `Arch.LIMM.IsLIMMConsistent` for the definition of consistency in LIMM.
module Proof.Elimination.FRAW.Consistent
  (dst : Execution LabelLIMM)
  (dst-ok : FRAW-Restricted dst)
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
-- Local imports: Proof Components
open import Proof.Elimination.FRAW.Execution dst dst-ok as FRAW-Ex
open import Proof.Elimination.FRAW.WellFormed dst dst-ok as FRAW-Wf
import Proof.Framework LabelLIMM dst dst-wf as Ψ
import Proof.Elimination.Framework dst dst-wf as Δ


-- General Proof Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Elimination Proof Framework
open Δ.Definitions δ
open Δ.WellFormed δ
-- Other
open FRAW-Restricted dst-ok
open TransformFRAW.Extra dst-ok
open Ex.Execution
open Ex.WellFormed
open FRAW-Ex.Extra
open IsLIMMConsistent


dst-consistent = consistent


-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result
--
--
-- For explanation, see also the proof for RAW. (In `Proof.Elimination.RAW.Consistent`)
--


-- # Definitions

ord-fence∈src : ∀ {P₁ P₂ : Pred (Event LabelLIMM) ℓzero} {m : F-mode} {x y : Event LabelLIMM}
  → ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ m ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x y
  → ∃[ z ] ( z ∈ events src × EvF₌ m z )
ord-fence∈src ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) =
  z , poˡ∈src po[zy] , z-f

src-elim-rᵣ : EvRᵣ src-elim-ev
src-elim-rᵣ with elim-skip
... | ev-skip with ℕ-dec elim-uid elim-uid
... | yes refl   = ev-r is-r refl
... | no uid≢uid = ⊥-elim (uid≢uid refl)

src-elim-r : EvR src-elim-ev
src-elim-r = rₜ⇒r src-elim-rᵣ

src-p₁e-sloc : SameLoc src-pres₁-ev src-elim-ev
src-p₁e-sloc = same-loc pres₁-has-loc src-elim-has-loc

poˡ-e⇒p : {y : Event LabelLIMM} → po src src-elim-ev y → po src src-pres₁-ev y
poˡ-e⇒p = po-trans src-wf po[p₁e]ˢ

plˡ-e⇒p : {y : Event LabelLIMM} → po-loc src src-elim-ev y → po-loc src src-pres₁-ev y
plˡ-e⇒p (po[ey] , ey-sloc) = poˡ-e⇒p po[ey] , trans-same-loc src-p₁e-sloc ey-sloc

poʳ-e⇒p₁ : {x : Event LabelLIMM} → x ≢ src-pres₁-ev → x ≢ src-pres₂-ev → po src x src-elim-ev → po src x src-pres₁-ev
poʳ-e⇒p₁ ¬x-pres₁ ¬x-pres₂ po[xe] =
  let po[xp₂] = ⊥⊎-elim ¬x-pres₂ id (unsplit-poʳ src-wf po[xe] pi[p₂e]ˢ)
  in ⊥⊎-elim ¬x-pres₁ id (unsplit-poʳ src-wf po[xp₂] pi[p₁p₂]ˢ)

plʳ-e⇒p₁ : {x : Event LabelLIMM} → x ≢ src-pres₁-ev → po-loc src x src-elim-ev → po-loc src x src-pres₁-ev
plʳ-e⇒p₁ {x} ¬x-pres₁ (po[xe] , xe-sloc@(same-loc x-loc _)) =
  let ¬x-pres₂ : x ≢ src-pres₂-ev
      ¬x-pres₂ = λ{x≡p₂ → ¬f-loc (subst EvF (≡-sym x≡p₂) pres₂-f) (_ , x-loc)}
  in poʳ-e⇒p₁ ¬x-pres₁ ¬x-pres₂ po[xe] , trans-same-loc xe-sloc (sym-same-loc p₁e-sloc)

¬pres₁-elim : src-pres₁-ev ≢ src-elim-ev
¬pres₁-elim p≡e = po-irreflexive src-wf p≡e po[p₁e]ˢ

rf-p₁e : rf src src-pres₁-ev src-elim-ev
rf-p₁e = rf-new refl refl

¬w-elim : {x : Event LabelLIMM} → EvW x → x ≢ src-elim-ev
¬w-elim x-w refl = disjoint-r/w _ (src-elim-r , x-w)


-- # Proof: Coherence

CohDetour : Rel (Event LabelLIMM) ℓzero
CohDetour x y = Coh src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)

coh[xey]→cohd⁺[xy] : ∀ {x y : Event LabelLIMM}
  → Coh src x src-elim-ev
  → Coh src src-elim-ev y
    --------------------------
  → TransClosure CohDetour x y
coh[xey]→cohd⁺[xy] {x} (coh-po-loc pl[xe]) (coh-po-loc pl[ey]) with ev-eq-dec x src-pres₁-ev
... | yes refl   = -- x ≡ p
  let ¬y-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[ey])}
  in [ coh-po-loc (plˡ-e⇒p pl[ey]) , ¬pres₁-elim , ¬y-elim ]
... | no ¬x-pres =
  let ¬x-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[xe])}
      ¬y-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[ey])}
  in (coh-po-loc (plʳ-e⇒p₁ ¬x-pres pl[xe]) , ¬x-elim , ¬pres₁-elim) ∷ [ ( coh-po-loc (plˡ-e⇒p pl[ey]) , ¬pres₁-elim , ¬y-elim ) ]
coh[xey]→cohd⁺[xy] {x} (coh-po-loc pl[xe]) (coh-fr fr[ey]@(rf⁻¹[ez] ⨾[ _ ]⨾ co[zy]))
  with wf-rf-≤1 src-wf _ _ _ rf⁻¹[ez] rf-p₁e -- z ≡ p
... | refl -- z ≡ p
  with ev-eq-dec x src-pres₁-ev
... | yes refl = -- x ≡ z ≡ p
   let ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
   in [ coh-co co[zy] , ¬pres₁-elim , ¬y-elim ] 
... | no ¬x-pres =
  let ¬x-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[xe])}
      ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
  in (coh-po-loc (plʳ-e⇒p₁ ¬x-pres pl[xe]) , ¬x-elim , ¬pres₁-elim) ∷ [ coh-co co[zy] , ¬pres₁-elim , ¬y-elim ]
coh[xey]→cohd⁺[xy] (coh-rf rf[xe])     (coh-po-loc pl[ey])
  with wf-rf-≤1 src-wf _ _ _ rf[xe] rf-p₁e -- x ≡ p
... | refl =
  let ¬y-elim = λ{refl → po-irreflexive src-wf refl (proj₁ pl[ey])}
  in [ coh-po-loc (plˡ-e⇒p pl[ey]) , ¬pres₁-elim , ¬y-elim ]
coh[xey]→cohd⁺[xy] (coh-rf rf[xe])     (coh-fr fr[ey]@(rf⁻¹[ez] ⨾[ _ ]⨾ co[zy]))
  with wf-rf-≤1 src-wf _ _ _ rf[xe] rf⁻¹[ez] -- x ≡ z
... | refl =
  let ¬z-elim = λ{refl → rf-irreflexive src-wf refl rf⁻¹[ez]}
      ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
  in [ coh-co co[zy] , ¬z-elim , ¬y-elim ]
coh[xey]→cohd⁺[xy] (coh-rf rf[xe])     (coh-rf rf[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (rf-w×r src-wf) rf[ey]))
coh[xey]→cohd⁺[xy] (coh-rf rf[xe])     (coh-co co[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (co-w×w src-wf) co[ey]))
coh[xey]→cohd⁺[xy] (coh-po-loc pl[xe]) (coh-rf rf[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (rf-w×r src-wf) rf[ey]))
coh[xey]→cohd⁺[xy] (coh-po-loc pl[xe]) (coh-co co[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (co-w×w src-wf) co[ey]))
coh[xey]→cohd⁺[xy] (coh-fr fr[xe])     _               = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (fr-r×w src-wf) fr[xe]))
coh[xey]→cohd⁺[xy] (coh-co co[xe])     _               = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (co-w×w src-wf) co[xe]))

-- |
--
-- General strategy:
-- * If the cycle goes through the eliminated event, identify it. Otherwise, it is a trivial detour.
-- * Divert all cases around the eliminated event
coh-detour : ∀ {x : Event LabelLIMM}
  → TransClosure (Coh src) x x
    ---------------------------------
  → ∃[ z ] TransClosure CohDetour z z
coh-detour coh⁺[xx] with divert-cycle coh⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
coh-detour coh⁺[xx] | inj₁ (cycle₁ coh[ee]) =
  ⊥-elim (coh-irreflexive src-wf refl coh[ee])
coh-detour coh⁺[xx] | inj₁ (cycle₂ {y} ¬elim-y coh[ey] coh[ye]) =
  (y , coh[xey]→cohd⁺[xy] coh[ye] coh[ey])
coh-detour coh⁺[xx] | inj₁ (cycleₙ {x} {y} coh[ex] cohd⁺[xy] coh[ye]) =
  (y , coh[xey]→cohd⁺[xy] coh[ye] coh[ex] ++ cohd⁺[xy])
coh-detour coh⁺[xx] | inj₂ cohd⁺[xx] = _ , cohd⁺[xx]

frˡ∈src : fr src ˡ∈src
frˡ∈src (rf⁻¹[xz] ⨾[ _ ]⨾ co[zy]) = rfʳ∈src rf⁻¹[xz]

fr[⇒] : CRel[⇒] (fr src) (fr dst)
fr[⇒] ¬x-elim ¬y-elim x∈src y∈src (rf⁻¹[xz] ⨾[ _ ]⨾ co[zy]) =
  let ¬z-elim = ¬w-elim (×₂-applyˡ (co-w×w src-wf) co[zy])
      z∈src = coˡ∈src co[zy]
  in rf[⇒] ¬z-elim ¬x-elim z∈src x∈src rf⁻¹[xz] ⨾[ _ ]⨾ co[⇒] ¬z-elim ¬y-elim z∈src y∈src co[zy]

src-ax-coherence : Acyclic _≡_ (Coh src)
src-ax-coherence refl coh⁺[xx] =
  let cohd⁺[zz] = proj₂ (coh-detour coh⁺[xx])
      z∈src = ⁺-lift-predˡ cohdˡ∈src cohd⁺[zz]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ cohdˡ∈src cohd[⇒]coh z∈src z∈src cohd⁺[zz])
  where
  cohd[⇒]coh : Rel[⇒] CohDetour (Coh dst)
  cohd[⇒]coh x∈src y∈src (coh-po-loc (po[xy] , xy-sloc) , ¬x-elim , ¬y-elim) =
    coh-po-loc (po[⇒] x∈src y∈src po[xy] , sloc[⇒] ¬x-elim ¬y-elim x∈src y∈src xy-sloc)
  cohd[⇒]coh x∈src y∈src (coh-rf rf[xy] , ¬x-elim , ¬y-elim) =
    coh-rf (rf[⇒] ¬x-elim ¬y-elim x∈src y∈src rf[xy])
  cohd[⇒]coh x∈src y∈src (coh-fr fr[xy] , ¬x-elim , ¬y-elim) =
    coh-fr (fr[⇒] ¬x-elim ¬y-elim x∈src y∈src fr[xy])
  cohd[⇒]coh x∈src y∈src (coh-co co[xy] , ¬x-elim , ¬y-elim) =
    coh-co (co[⇒] ¬x-elim ¬y-elim x∈src y∈src co[xy])
  
  cohdˡ∈src : CohDetour ˡ∈src
  cohdˡ∈src (coh[xy] , _ , _) = cohˡ∈ex src-wf coh[xy]


-- # Proof: Atomicity

fre[⇒] : CRel[⇒] (fre src) (fre dst)
fre[⇒] ¬x-elim ¬y-elim x∈src y∈src (fr[xy] , ¬po[xy]) =
  fr[⇒] ¬x-elim ¬y-elim x∈src y∈src fr[xy] , ¬po[⇒] x∈src y∈src ¬po[xy]

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy]))
  with ev-eq-dec x src-elim-ev
... | no ¬elim-x =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
      ¬elim-z = ¬w-elim (×₂-applyˡ (co-w×w src-wf) (proj₁ coe[zy]))
      ¬elim-y = ¬w-elim (×₂-applyʳ (co-w×w src-wf) (proj₁ coe[zy]))
      dst-rmw[xy] = rmw[⇒] x∈src y∈src rmw[xy]
      dst-fre[xz] = fre[⇒] ¬elim-x ¬elim-z x∈src z∈src fre[xz]
      dst-coe[zy] = coe[⇒] ¬elim-z ¬elim-y z∈src y∈src coe[zy]
  in ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src) (dst-rmw[xy] , (dst-fre[xz] ⨾[ _ ]⨾ dst-coe[zy]))
... | yes refl = lemma rmw[xy] refl
  where
  lemma : ∀ {x y : Event LabelLIMM} → rmw src x y → x ≢ src-elim-ev
  lemma rmw[xy] refl = disjoint-rₜ _ (src-elim-rᵣ , ×₂-applyˡ (rmw-r×w src-wf) rmw[xy])


-- # Proof: Global Order

GhbiAltDetour : Rel (Event LabelLIMM) ℓzero
GhbiAltDetour x y = GhbiAlt src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)

¬pres₁-init : ¬ EvInit src-pres₁-ev
¬pres₁-init p₁-init = disjoint-wₙ/init _ (wₙₜ⇒wₙ pres₁-wₙᵣ , p₁-init)

¬pres₂-init : ¬ EvInit src-pres₂-ev
¬pres₂-init p₂-init = disjoint-f/init _ (pres₂-f , p₂-init)

poˡ-p₁⇒e : {y : Event LabelLIMM} → y ≢ src-pres₂-ev → y ≢ src-elim-ev → po src src-pres₁-ev y → po src src-elim-ev y
poˡ-p₁⇒e {y} ¬y-pres₂ ¬y-elim po[p₁y] =
  let po[p₂y] : po src src-pres₂-ev y
      po[p₂y] = ⊥⊎-elim (≢-sym ¬y-pres₂) id (unsplit-poˡ src-wf ¬pres₁-init po[p₁y] pi[p₁p₂]ˢ)
  in ⊥⊎-elim (≢-sym ¬y-elim) id (unsplit-poˡ src-wf ¬pres₂-init po[p₂y] pi[p₂e]ˢ)

¬poˡ-e⇒p₁ : {y : Event LabelLIMM} → y ≢ src-pres₂-ev → y ≢ src-elim-ev → ¬ po src src-elim-ev y → ¬ po src src-pres₁-ev y
¬poˡ-e⇒p₁ = contrapositive ∘₂ poˡ-p₁⇒e

fr[ey]→co[py] : {y : Event LabelLIMM} → fr src src-elim-ev y → co src src-pres₁-ev y
fr[ey]→co[py] (rf⁻¹[ez] ⨾[ _ ]⨾ co[zy]) with wf-rf-≤1 src-wf _ _ _ rf-p₁e rf⁻¹[ez]
... | refl = co[zy]


ordˡ-e⇒p : {y : Event LabelLIMM} → OrdAlt src src-elim-ev y → OrdAlt src src-pres₁-ev y
ordˡ-e⇒p (ord-rm ((refl , _) ⨾[ _ ]⨾ po[ez] ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw))) =
  let po[p₂y] = po-trans src-wf (proj₁ pi[p₂e]ˢ) (po-trans src-wf po[ez] po[zy])
  in ord-sc ((refl , w⇒rw pres₁-w) ⨾[ _ ]⨾ proj₁ pi[p₁p₂]ˢ ⨾[ _ ]⨾ (refl , pres₂-f₌) ⨾[ _ ]⨾ po[p₂y] ⨾[ _ ]⨾ (refl , y-rw))
ordˡ-e⇒p (ord-sc ((refl , _) ⨾[ _ ]⨾ po[ez] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw))) =
  let po[p₂y] = po-trans src-wf (proj₁ pi[p₂e]ˢ) (po-trans src-wf po[ez] po[zy])
  in ord-sc ((refl , w⇒rw pres₁-w) ⨾[ _ ]⨾ proj₁ pi[p₁p₂]ˢ ⨾[ _ ]⨾ (refl , pres₂-f₌) ⨾[ _ ]⨾ po[p₂y] ⨾[ _ ]⨾ (refl , y-rw))
ordˡ-e⇒p (ord-rmw-dom ((refl , e-rw) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y∈rmwˡ))) =
  let po[p₁y] = poˡ-e⇒p po[ey]
  in ord-rmw-dom ((refl , w⇒rw pres₁-w) ⨾[ _ ]⨾ po[p₁y] ⨾[ _ ]⨾ (refl , y∈rmwˡ))
ordˡ-e⇒p (ord-w ((refl , e-rw) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-wₜ))) =
  ord-w ((refl , w⇒rw pres₁-w) ⨾[ _ ]⨾ poˡ-e⇒p po[ey] ⨾[ _ ]⨾ (refl , y-wₜ))
-- Impossible cases
ordˡ-e⇒p (ord-init ((refl , e-init) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-rw))) =
  ⊥-elim (disjoint-r/init _ (src-elim-r , e-init))
ordˡ-e⇒p (ord-ww ww[ey]) =
  ⊥-elim (disjoint-r/w _ (src-elim-r , ord-predˡ src ww[ey]))
ordˡ-e⇒p (ord-rmw-codom ((refl , e∈rmwʳ) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-rw))) =
  ⊥-elim (disjoint-r/w _ (src-elim-r , wₜ⇒w (rmwʳ-w src-wf e∈rmwʳ)))
ordˡ-e⇒p (ord-r ((refl , e-rₜ) ⨾[ _ ]⨾ po[ey] ⨾[ _ ]⨾ (refl , y-rw))) =
  ⊥-elim (disjoint-rₜ _ (src-elim-rᵣ , e-rₜ))


src-po-r-rmʳ : {x : Event LabelLIMM} → x ≢ src-elim-ev → x ∈ events src → EvRᵣ x → ∃[ y ] (EvF₌ RM y × po-imm src x y)
src-po-r-rmʳ ¬x-elim x∈src x-r with po-r-rmʳ (events[⇒] x∈src) (Rₜ[⇒] ¬x-elim x∈src x-r)
... | z , z-f , pi[xz] =
  let x∈dst = events[⇒] x∈src
      z∈dst = piʳ∈ex dst-wf pi[xz]
      z∈src = events[⇐] z∈dst
  in ev[⇐] z∈dst , F₌[⇐] z∈dst z-f , pi[⇐$] x∈src (events[⇐] z∈dst) pi[xz]

¬init+wₜ⇒wₙₜ : {Label : Set} {{_ : LabelClass Label}}
  → {tag : Tag} → {x : Event Label} → ¬ EvInit x → EvWₜ tag x → EvWₙₜ tag x
¬init+wₜ⇒wₙₜ ¬x-init (ev-init refl) = ⊥-elim (¬x-init ev-init)
¬init+wₜ⇒wₙₜ ¬x-init (ev-w lab tag≡tag) = ev-w lab tag≡tag


wₙₜ⇒¬init : {Label : Set} {{_ : LabelClass Label}}
  → {x : Event Label} {tag : Tag} → EvWₙₜ tag x → ¬ EvInit x
wₙₜ⇒¬init (ev-w _ _) ()


Wₙᵣ[⇒] : CPred[⇒]² (EvWₙₜ tmov)
Wₙᵣ[⇒] ¬x-elim x∈src x-wₙᵣ =
  let xˢ-wᵣ = wₙₜ⇒wₜ x-wₙᵣ
      xᵗ-wᵣ = Wₜ[⇒] ¬x-elim x∈src xˢ-wᵣ
      xᵗ-¬init = ¬Init[⇒] x∈src (wₙₜ⇒¬init x-wₙᵣ)
  in ¬init+wₜ⇒wₙₜ xᵗ-¬init xᵗ-wᵣ

src-po-w-wwˡ : {y : Event LabelLIMM} → y ≢ src-elim-ev → y ∈ events src → EvWₙₜ tmov y → ∃[ x ] (EvF₌ WW x × po-imm src x y)
src-po-w-wwˡ ¬y-elim y∈src yˢ-wₙᵣ =
  let yᵗ-wₙᵣ = Wₙᵣ[⇒] ¬y-elim y∈src yˢ-wₙᵣ
      y∈dst = events[⇒] y∈src
      (x , x-ww , pi[xy]) = po-w-wwˡ y∈dst yᵗ-wₙᵣ
      x∈dst = piˡ∈ex dst-wf pi[xy]
  in _ , F₌[⇐] x∈dst x-ww , subst-rel (po-imm src) refl (≡-sym (ev[⇒⇐] y∈src)) (pi[⇐] x∈dst y∈dst pi[xy])



ordWWʳ-e⇒p₁ : {x : Event LabelLIMM}
  → x ≢ src-pres₁-ev
  → ( ⦗ EvRW ⦘ ⨾ po src ⨾ ⦗ EvF₌ SC ⦘ ⨾ po src ⨾ ⦗ EvRW ⦘ ) x src-elim-ev
  → OrdAlt src x src-pres₁-ev
ordWWʳ-e⇒p₁ {x} ¬x-pres₁ ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ z ]⨾ po[ze] ⨾[ _ ]⨾ (refl , e-rw)) =
  ⊎-elim (λ{z≡p₁ → lemma₂ (subst-rel (po src) refl z≡p₁ po[xz])}) lemma₁ (unsplit-poʳ src-wf po[ze] pi[p₂e]ˢ)
  where
  lemma₁ : po src z src-pres₂-ev → OrdAlt src x src-pres₁-ev
  lemma₁ po[zp₂] =
    let ¬z-pres₁ = λ{z≡p₁ → disjoint-f/w _ (subst EvF z≡p₁ (f₌⇒f z-sc) , pres₁-w)}
        po[zp₁] = ⊥⊎-elim ¬z-pres₁ id (unsplit-poʳ src-wf po[zp₂] pi[p₁p₂]ˢ)
    in ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zp₁] ⨾[ _ ]⨾ (refl , w⇒rw pres₁-w))

  lemma₂ : po src x src-pres₂-ev → OrdAlt src x src-pres₁-ev
  lemma₂ po[xp₂] =
    let po[xp₁] : po src x src-pres₁-ev
        po[xp₁] = ⊥⊎-elim ¬x-pres₁ id (unsplit-poʳ src-wf po[xp₂] pi[p₁p₂]ˢ)
        ¬x-elim = λ{x≡e → po-irreflexive src-wf x≡e (po-trans src-wf po[xz] po[ze])}
        x∈src = poˡ∈ex src-wf po[xp₁]
    in
    case rw/rw x-rw of
    λ{ (inj₁ x-r) →
         case r/tag x-r of
         λ{ (inj₁ x-rᵣ) →
              let ¬x-init = λ{x-init → disjoint-r/init _ (x-r , x-init)}
                  (y , y-rm , pi[xy]) = src-po-r-rmʳ ¬x-elim x∈src x-rᵣ
                  ¬y-pres₁ = λ{y≡p₁ → disjoint-f/w _ (subst EvF y≡p₁ (f₌⇒f y-rm) , pres₁-w)}
                  po[yp₁] = ⊥⊎-elim ¬y-pres₁ id (unsplit-poˡ src-wf ¬x-init po[xp₁] pi[xy])
              in ord-rm ((refl , x-r) ⨾[ _ ]⨾ proj₁ pi[xy] ⨾[ _ ]⨾ (refl , y-rm) ⨾[ _ ]⨾ po[yp₁] ⨾[ _ ]⨾ (refl , w⇒rw pres₁-w))
          ; (inj₂ x-rₐ) →
              ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , w⇒rw pres₁-w))
          }
     ; (inj₂ x-w) →
         let (y , y-ww , pi[yp₁]) = src-po-w-wwˡ ¬pres₁-elim pres₁∈src pres₁-wₙᵣ
             x≢y = λ{x≡y → disjoint-f/w _ (f₌⇒f y-ww , subst EvW x≡y x-w)}
             po[xy] = ⊥⊎-elim x≢y id (unsplit-poʳ src-wf po[xp₁] pi[yp₁])
         in ord-ww ((refl , x-w) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-ww) ⨾[ _ ]⨾ proj₁ pi[yp₁] ⨾[ _ ]⨾ (refl , pres₁-w))
     }


ordʳ-e⇒p : {x : Event LabelLIMM} → x ≢ src-pres₁-ev → OrdAlt src x src-elim-ev → OrdAlt src x src-pres₁-ev
ordʳ-e⇒p ¬x-pres₁ (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬x-pres₂ = λ{x≡p₂ → disjoint-f/init _ (subst EvF (≡-sym x≡p₂) pres₂-f , x-init)}
      po[xp₁] = poʳ-e⇒p₁ ¬x-pres₁ ¬x-pres₂ po[xe]
  in ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , w⇒rw pres₁-w))
ordʳ-e⇒p _ (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[ze] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬z-pres₁ = λ{z≡p₁ → disjoint-f/w _ (subst EvF z≡p₁ (f₌⇒f z-rm) , pres₁-w)}
      ¬z-pres₂ = λ{z≡p₂ → disjoint-f/mode (λ()) _ (pres₂-f₌ , subst (EvF₌ RM) z≡p₂ z-rm)}
      po[zp₁] = poʳ-e⇒p₁ ¬z-pres₁ ¬z-pres₂ po[ze]
  in ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zp₁] ⨾[ _ ]⨾ (refl , w⇒rw pres₁-w))
ordʳ-e⇒p ¬x-pres₁ (ord-sc sc[xe]) = ordWWʳ-e⇒p₁ ¬x-pres₁ sc[xe]
ordʳ-e⇒p ¬x-pres₁ (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e∈rmwˡ))) =
  ⊥-elim (disjoint-rₜ _ (src-elim-rᵣ , rmwˡ-r src-wf e∈rmwˡ))
ordʳ-e⇒p ¬x-pres₁ (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬x-pres₂ = λ{x≡p₂ → disjoint-f/w _ (pres₂-f , subst EvW x≡p₂ (wₜ⇒w (rmwʳ-w src-wf x∈rmwʳ)))}
      po[xp₁] = poʳ-e⇒p₁ ¬x-pres₁ ¬x-pres₂ po[xe]
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , w⇒rw pres₁-w))
ordʳ-e⇒p ¬x-pres₁ (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-wₐ))) =
  ⊥-elim (disjoint-r/w _ (src-elim-r , wₜ⇒w e-wₐ))
ordʳ-e⇒p ¬x-pres₁ (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬x-pres₂ = λ{x≡p₂ → disjoint-f/r _ (pres₂-f , subst EvR x≡p₂ (rₜ⇒r x-rₐ))}
      po[xp₁] = poʳ-e⇒p₁ ¬x-pres₁ ¬x-pres₂ po[xe]
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , w⇒rw pres₁-w))
-- Impossible cases
ordʳ-e⇒p ¬x-pres₁ (ord-ww ww[xe]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ord-predʳ src ww[xe]))


frˡ-e⇒coˡ-p : {y : Event LabelLIMM} → fr src src-elim-ev y → co src src-pres₁-ev y
frˡ-e⇒coˡ-p (rf⁻¹[ez] ⨾[ _ ]⨾ co[zy]) with wf-rf-≤1 src-wf _ _ _ rf⁻¹[ez] rf-p₁e
... | refl = co[zy]

freˡ-e⇒coeˡ-p : {y : Event LabelLIMM} → fre src src-elim-ev y → coe src src-pres₁-ev y
freˡ-e⇒coeˡ-p (fr[ey] , ¬po[ey]) =
  let ¬y-elim = λ{y≡e → fr-irreflexive src-wf (≡-sym y≡e) fr[ey]}
      ¬y-pres₂ = λ{y≡p₂ → disjoint-f/w _ (pres₂-f , subst EvW y≡p₂ (×₂-applyʳ (fr-r×w src-wf) fr[ey]))}
  in frˡ-e⇒coˡ-p fr[ey] , ¬poˡ-e⇒p₁ ¬y-pres₂ ¬y-elim ¬po[ey]


ghbiˡ-e⇒p : {y : Event LabelLIMM} → GhbiAlt src src-elim-ev y → GhbiAlt src src-pres₁-ev y
ghbiˡ-e⇒p (ghbi-ord ord[ey]) = ghbi-ord (ordˡ-e⇒p ord[ey])
ghbiˡ-e⇒p (ghbi-fre fre[ey]) = ghbi-coe (freˡ-e⇒coeˡ-p fre[ey])
-- impossible cases
ghbiˡ-e⇒p (ghbi-rfe rfe[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (rfe-w×r src-wf) rfe[ey]))
ghbiˡ-e⇒p (ghbi-coe coe[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (coe-w×w src-wf) coe[ey]))


ghbiʳ-e⇒p : {x : Event LabelLIMM} → x ≢ src-pres₁-ev → GhbiAlt src x src-elim-ev → GhbiAlt src x src-pres₁-ev
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-ord ord[xe]) = ghbi-ord (ordʳ-e⇒p ¬x-pres₁ ord[xe])
-- impossible cases
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-rfe rfe[xe]) = ⊥-elim (¬x-pres₁ (wf-rf-≤1 src-wf _ _ _ (proj₁ rfe[xe]) rf-p₁e))
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-coe coe[xe]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (coe-w×w src-wf) coe[xe]))
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-fre fre[xe]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (fre-r×w src-wf) fre[xe]))


ghb-detour : ∀ {x : Event LabelLIMM} → TransClosure (GhbiAlt src) x x → ∃[ z ] TransClosure GhbiAltDetour z z
ghb-detour {x} ghbi⁺[xx] with divert-cycle ghbi⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
... | inj₁ (cycle₁ ghbi[xx]) = ⊥-elim (¬ghbi-cycle₁ src-wf ghbi[xx])
... | inj₁ (cycle₂ ¬x-elim ghbi[ex] ghbi[xe])    =
  ⊥-elim (¬ghbi-cycle₂ src-wf src-ax-coherence ghbi[ex] ghbi[xe])
... | inj₁ (cycleₙ {x} {y} ghbi[ex] ghbid⁺[xy] ghbi[ye]) =
  let ¬x-elim = ⁺-lift-predˡ (proj₁ ∘ proj₂) ghbid⁺[xy]
      ¬y-elim = ⁺-lift-predʳ (proj₂ ∘ proj₂) ghbid⁺[xy]
  in
  case ev-eq-dec y src-pres₁-ev of
  λ{ (yes refl) →
       _ , (ghbiˡ-e⇒p ghbi[ex] , ¬pres₁-elim , ¬x-elim) ∷ ghbid⁺[xy]
   ; (no ¬y-pres₁) →
       _ , (ghbiʳ-e⇒p ¬y-pres₁ ghbi[ye] , ¬y-elim , ¬pres₁-elim) ∷ (ghbiˡ-e⇒p ghbi[ex] , ¬pres₁-elim , ¬x-elim) ∷ ghbid⁺[xy]
   }
... | inj₂ ghbid⁺[xx] = (_ , ghbid⁺[xx])


ghbidˡ∈src : GhbiAltDetour ˡ∈src
ghbidˡ∈src (ghbi[xy] , _ , _) = GhbiAltˡ∈ex src-wf ghbi[xy]


ghbi[⇒] : Rel[⇒] GhbiAltDetour (GhbiAlt dst)
ghbi[⇒] x∈src y∈src (ghbi-ord ord[xy] , ¬elim-x , ¬elim-y) = ghbi-ord (ord[⇒] ¬elim-x ¬elim-y x∈src y∈src ord[xy])
ghbi[⇒] x∈src y∈src (ghbi-rfe rfe[xy] , ¬elim-x , ¬elim-y) = ghbi-rfe (rfe[⇒] ¬elim-x ¬elim-y x∈src y∈src rfe[xy])
ghbi[⇒] x∈src y∈src (ghbi-coe coe[xy] , ¬elim-x , ¬elim-y) = ghbi-coe (coe[⇒] ¬elim-x ¬elim-y x∈src y∈src coe[xy])
ghbi[⇒] x∈src y∈src (ghbi-fre fre[xy] , ¬elim-x , ¬elim-y) = ghbi-fre (fre[⇒] ¬elim-x ¬elim-y x∈src y∈src fre[xy])


src-ax-global-ord : Irreflexive _≡_ (ghb src)
src-ax-global-ord refl ghb[xx] =
  -- First, find a detour that only goes between R/W events. Then find a detour that does /not/ go
  -- through the eliminated event.
  let (y , ghbd[yy]) = ghb-detour (proj₂ (detour src-wf ghb[xx]))
      y∈src = ⁺-lift-predˡ (GhbiAltˡ∈ex src-wf ∘ proj₁) ghbd[yy]
  in ax-global-ord dst-consistent refl (GhbiAlt⁺⇒Ghbi⁺ (⁺[⇒]ˡ ghbidˡ∈src ghbi[⇒] y∈src y∈src ghbd[yy]))


-- # Result: Consistent

src-consistent : IsLIMMConsistent src
src-consistent =
  record
    { ax-coherence  = src-ax-coherence
    ; ax-atomicity  = src-ax-atomicity
    ; ax-global-ord = src-ax-global-ord
    }
