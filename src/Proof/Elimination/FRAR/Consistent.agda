{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.LIMM using (LabelLIMM)
open import TransformFRAR using (FRAR-Restricted)


module Proof.Elimination.FRAR.Consistent
  (dst : Execution LabelLIMM)
  (dst-ok : FRAR-Restricted dst)
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
open import Proof.Elimination.FRAR.Execution dst dst-ok as FRAR-Ex
open import Proof.Elimination.FRAR.WellFormed dst dst-ok as FRAR-Wf
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
open FRAR-Ex.Extra
open IsLIMMConsistent
open TransformFRAR.Extra dst-ok
open FRAR-Restricted dst-ok


private
  dst-consistent = consistent


-- File structure
-- * Definitions
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result


-- # Helpers

poʳ-e⇒p₂ : {x : Event LabelLIMM}
  → x ≢ pres₂-ev
  → po src x src-elim-ev
  → po src x pres₂-ev
poʳ-e⇒p₂ ¬x-pres₂ po[xe] =
  ⊥⊎-elim ¬x-pres₂ id (unsplit-poʳ src-wf po[xe] src-pair₂-pi)


poʳ-e⇒p₁ : {x : Event LabelLIMM}
  → x ≢ pres₁-ev
  → x ≢ pres₂-ev
  → po src x src-elim-ev
  → po src x pres₁-ev
poʳ-e⇒p₁ ¬x-pres₁ ¬x-pres₂ po[xe] =
  ⊥⊎-elim ¬x-pres₁ id (unsplit-poʳ src-wf (poʳ-e⇒p₂ ¬x-pres₂ po[xe]) src-pair₁-pi)


poˡ-e⇒p :{y : Event LabelLIMM} → po src src-elim-ev y → po src pres₁-ev y
poˡ-e⇒p po[ey] = po-trans src-wf src-pair₁₂-po po[ey]


plˡ-e⇒p : ∀ {y : Event LabelLIMM} → po-loc src src-elim-ev y → po-loc src pres₁-ev y
plˡ-e⇒p (po[ey] , ey-sloc) = (poˡ-e⇒p po[ey] , trans-same-loc pe-sloc ey-sloc)


plʳ-e⇒p₁ : ∀ {x : Event LabelLIMM}
  → x ≢ pres₁-ev
  → po-loc src x src-elim-ev
  → po-loc src x pres₁-ev
plʳ-e⇒p₁ ¬x-pres₁ (po[xe] , xe-sloc@(same-loc x-loc _)) =
  let ¬x-pres₂ = λ{refl → ¬f-loc pres₂-f (_ , x-loc)}
  in (poʳ-e⇒p₁ ¬x-pres₁ ¬x-pres₂ po[xe] , trans-same-loc xe-sloc (sym-same-loc pe-sloc))


pres₁-rw : EvRW pres₁-ev
pres₁-rw = r⇒rw pres₁-r


ord-fence : ∀ {P₁ P₂ : Pred (Event LabelLIMM) ℓzero} {m : F-mode} {x y : Event LabelLIMM}
  → ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ m ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x y
  → Event LabelLIMM
ord-fence ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) =
  z
  
ord-fence∈src : ∀ {P₁ P₂ : Pred (Event LabelLIMM) ℓzero} {m : F-mode} {x y : Event LabelLIMM}
  → (f[xy] : ( ⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ m ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x y)
  → ord-fence f[xy] ∈ events src
ord-fence∈src ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) =
  poˡ∈src po[zy] 


ord-fence-F : ∀ {P₁ P₂ : Pred (Event LabelLIMM) ℓzero} {m : F-mode} {x y : Event LabelLIMM}
  → (f[xy] : (⦗ P₁ ⦘ ⨾ po src ⨾ ⦗ EvF₌ m ⦘ ⨾ po src ⨾ ⦗ P₂ ⦘ ) x y)
  → EvF₌ m (ord-fence f[xy])
ord-fence-F ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) = z-f


-- # Coherence

CohDetour : Rel (Event LabelLIMM) ℓzero
CohDetour x y = Coh src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)

cohˡ-e⇒p : {y : Event LabelLIMM} → Coh src src-elim-ev y → Coh src pres₁-ev y
cohˡ-e⇒p (coh-po-loc pl[ey]) = coh-po-loc (plˡ-e⇒p pl[ey])
cohˡ-e⇒p (coh-fr fr[ey])     = coh-fr (frˡ-e⇒p fr[ey])
cohˡ-e⇒p (coh-rf rf[ey])     = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (rf-w×r src-wf) rf[ey]))
cohˡ-e⇒p (coh-co co[ey])     = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (co-w×w src-wf) co[ey]))

cohʳ-e⇒p : {x : Event LabelLIMM} → x ≢ pres₁-ev → Coh src x src-elim-ev → Coh src x pres₁-ev
cohʳ-e⇒p ¬x-pres₁ (coh-po-loc pl[xe]) = coh-po-loc (plʳ-e⇒p₁ ¬x-pres₁ pl[xe])
cohʳ-e⇒p ¬x-pres₁ (coh-rf rf[xe])     = coh-rf (rfʳ-e⇒p rf[xe])
cohʳ-e⇒p ¬x-pres₁ (coh-fr fr[xe])     = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (fr-r×w src-wf) fr[xe]))
cohʳ-e⇒p ¬x-pres₁ (coh-co co[xe])     = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (co-w×w src-wf) co[xe]))


coh-detour : ∀ {x : Event LabelLIMM} → TransClosure (Coh src) x x → ∃[ z ] TransClosure CohDetour z z
coh-detour coh⁺[xx] with divert-cycle coh⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
coh-detour coh⁺[xx] | inj₁ (cycle₁ coh[ee]) = ⊥-elim (coh-irreflexive src-wf refl coh[ee])
coh-detour coh⁺[xx] | inj₁ (cycle₂ {y} ¬y-elim coh[ey] coh[ye]) =
  let ¬y-pres₁ = λ{refl → coh-irreflexive src-wf refl (cohˡ-e⇒p coh[ey])}
  in _ , ((cohˡ-e⇒p coh[ey] , ¬pres₁-elimₛ , ¬y-elim)) ∷ [ cohʳ-e⇒p ¬y-pres₁ coh[ye] , ¬y-elim , ¬pres₁-elimₛ ]
coh-detour coh⁺[xx] | inj₁ (cycleₙ {x} {y} coh[ex] cohd⁺[xy] coh[ye])
  with ev-eq-dec y pres₁-ev
... | yes refl   =
  _ , (cohˡ-e⇒p coh[ex] , ¬pres₁-elimₛ , ⁺-lift-predˡ (proj₁ ∘ proj₂) cohd⁺[xy]) ∷ cohd⁺[xy] -- y ≡ p
... | no ¬pres-y =
  let ¬elim-y = ⁺-lift-predʳ (proj₂ ∘ proj₂) cohd⁺[xy]
      ¬elim-x = ⁺-lift-predˡ (proj₁ ∘ proj₂) cohd⁺[xy]
  in _ , ((cohʳ-e⇒p ¬pres-y coh[ye] , ¬elim-y , ¬pres₁-elimₛ) ∷ (cohˡ-e⇒p coh[ex] , ¬pres₁-elimₛ , ¬elim-x) ∷ cohd⁺[xy])
coh-detour coh⁺[xx] | inj₂ cohd⁺[xx] = _ , cohd⁺[xx]


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
      ¬elim-x = λ{refl → disjoint-rₜ _ (src-elim-rₜ , ×₂-applyˡ (rmw-r×w src-wf) rmw[xy])}
      ¬elim-y = elim-¬w (src-coʳ-w (proj₁ coe[zy]))
      ¬elim-z = elim-¬w (src-coˡ-w (proj₁ coe[zy]))
  in
  ax-atomicity dst-consistent (ev[⇒] x∈src) (ev[⇒] y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] ¬elim-x x∈src z∈src fre[xz] ⨾[ ev[⇒] z∈src ]⨾ coe[⇒] ¬elim-z ¬elim-y z∈src y∈src coe[zy]
    )


-- # Consistency

GhbiAltDetour : Rel (Event LabelLIMM) ℓzero
GhbiAltDetour x y = GhbiAlt src x y × (x ≢ src-elim-ev) × (y ≢ src-elim-ev)


¬elim-pres₂ : src-elim-ev ≢ pres₂-ev
¬elim-pres₂ e≡p₂ = po-irreflexive src-wf (≡-sym e≡p₂) (proj₁ src-pair₂-pi)


¬po[ep₁] : ¬ po src src-elim-ev pres₁-ev
¬po[ep₁] po[ep₁] = po-irreflexive src-wf refl (po-trans src-wf po[ep₁] src-pair₁₂-po)


pi[p₁p₂] : po-imm src pres₁-ev pres₂-ev
pi[p₁p₂] = src-pair₁-pi


pi[p₂e] : po-imm src pres₂-ev src-elim-ev
pi[p₂e] = src-pair₂-pi


po[p₁e] : po src pres₁-ev src-elim-ev
po[p₁e] = src-pair₁₂-po


poʳ-e⇒p : {x : Event LabelLIMM}
  → EvRW x
  → x ≢ pres₁-ev
  → po src x src-elim-ev
  → po src x pres₁-ev
poʳ-e⇒p {x} x-rw ¬x-pres₁ po[xe] =
  ⊥⊎-elim (λ{refl → disjoint-f/rw _ (pres₂-f , x-rw)}) lemma (unsplit-poʳ src-wf po[xe] pi[p₂e])
  where
  lemma : po src x pres₂-ev → po src x pres₁-ev
  lemma po[xp₂] = ⊥⊎-elim ¬x-pres₁ id (unsplit-poʳ src-wf po[xp₂] pi[p₁p₂])


src-po-r-rm : {x : Event LabelLIMM} → x ≢ src-elim-ev → x ∈ events src → EvRᵣ x → ∃[ y ] (EvF₌ RM y × po-imm src x y)
src-po-r-rm ¬x-elim x∈src x-r with po-r-rm (events[⇒] x∈src) (Rₜ[⇒] ¬x-elim x∈src x-r)
... | z , z-f , pi[xz] =
  let x∈dst = events[⇒] x∈src
      z∈dst = piʳ∈ex dst-wf pi[xz]
      z∈src = events[⇐] z∈dst
  in ev[⇐] z∈dst , F₌[⇐] z∈dst z-f , pi[⇐$] x∈src (events[⇐] z∈dst) pi[xz]


ordRM-e⇒p₁ : {x : Event LabelLIMM}
  → x ≢ pres₁-ev
  → ( ⦗ EvRᵣ ⦘ ⨾ po src ⨾ ⦗ EvF₌ RM ⦘ ⨾ po src ) x src-elim-ev
  → OrdAlt src x pres₁-ev
ordRM-e⇒p₁ {x} ¬x-pres₁ ((refl , x-rᵣ) ⨾[ x ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ y ]⨾ po[ye]) =
  -- Somehow, type checking can be /really really really/ slow on some of these equalities.
  -- I'm not sure what's causing that. To avoid it, I've added some type annotations, and
  -- avoid pattern-matching on `refl`. Seems to work..
  ⊎-elim
    (λ{y≡p → lemma₁ (subst-rel (po src) refl y≡p po[xy])})
    lemma₂
    (unsplit-poʳ src-wf po[ye] pi[p₂e])
  where
  lemma₁ : po src x pres₂-ev → OrdAlt src x pres₁-ev
  lemma₁ po[xp₂] =
    let po[xp₁] : po src x pres₁-ev
        po[xp₁] = ⊥⊎-elim ¬x-pres₁ id (unsplit-poʳ src-wf po[xp₂] pi[p₁p₂])
        x∈src : x ∈ events src
        x∈src = poˡ∈src po[xy]
        ¬x-elim : x ≢ src-elim-ev
        ¬x-elim = λ{x≡e → po-irreflexive src-wf x≡e (po-trans src-wf po[xy] po[ye])}
        ¬x-init : ¬ EvInit x
        ¬x-init = λ{x-init → disjoint-r/init _ (rₜ⇒r x-rᵣ , x-init)}
        (z , z-rm , pi[xz]) = src-po-r-rm ¬x-elim x∈src x-rᵣ
        τ₂ : ( z ≡ pres₁-ev ) ⊎ ( po src z pres₁-ev )
        τ₂ = unsplit-poˡ src-wf ¬x-init po[xp₁] pi[xz]
        po[zp₁] : po src z pres₁-ev
        po[zp₁] = ⊥⊎-elim (λ{z≡p₁ → disjoint-f/r _ (f₌⇒f z-rm , subst EvR (≡-sym z≡p₁) pres₁-r)}) id τ₂
    in
    ord-rm ((refl , rₜ⇒r x-rᵣ) ⨾[ _ ]⨾ proj₁ pi[xz] ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zp₁] ⨾[ _ ]⨾ (refl , r⇒rw pres₁-r))
  lemma₂ : po src y pres₂-ev → OrdAlt src x pres₁-ev
  lemma₂ po[yp₂] =
    let τ : (y ≡ pres₁-ev) ⊎ po src y pres₁-ev
        τ = unsplit-poʳ src-wf po[yp₂] pi[p₁p₂]
        po[yp₁] : po src y pres₁-ev
        po[yp₁] = ⊥⊎-elim (λ{y≡p₁ → disjoint-f/r _ (f₌⇒f y-f , subst EvR (≡-sym y≡p₁) pres₁-r)}) id τ
    in
    ord-rm ((refl , rₜ⇒r x-rᵣ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[yp₁] ⨾[ _ ]⨾ (refl , r⇒rw pres₁-r))


unsplitʳ-p₁p₂ : {x : Event LabelLIMM}
  → x ≢ pres₁-ev
  → x ≢ pres₂-ev
  → po src x src-elim-ev
  → po src x pres₁-ev
unsplitʳ-p₁p₂ ¬x-pres₁ ¬x-pres₂ po[xe] =
  let po[xp₂] = ⊥⊎-elim ¬x-pres₂ id (unsplit-poʳ src-wf po[xe] pi[p₂e])
  in ⊥⊎-elim ¬x-pres₁ id (unsplit-poʳ src-wf po[xp₂] pi[p₁p₂])


unsplitˡ-p₁p₂ : {y : Event LabelLIMM}
  → y ≢ pres₂-ev
  → y ≢ src-elim-ev
  → po src pres₁-ev y
  → po src src-elim-ev y
unsplitˡ-p₁p₂ {y} ¬y-pres₂ ¬y-elim po[p₁y] =
  let ¬pres₁-init = λ{p₁-init → disjoint-r/init _ (pres₁-r , p₁-init)}
      ¬pres₂-init = λ{p₂-init → disjoint-f/init _ (pres₂-f , p₂-init)}
      po[p₂y] : po src pres₂-ev y
      po[p₂y] = ⊥⊎-elim (≢-sym ¬y-pres₂) id (unsplit-poˡ src-wf ¬pres₁-init po[p₁y] pi[p₁p₂])
  in ⊥⊎-elim (≢-sym ¬y-elim) id (unsplit-poˡ src-wf ¬pres₂-init po[p₂y] pi[p₂e])


ordSC-e⇒p₁ : {x : Event LabelLIMM}
  → x ≢ pres₁-ev
  → ( ⦗ EvRW ⦘ ⨾ po src ⨾ ⦗ EvF₌ SC ⦘ ⨾ po src ) x src-elim-ev
  → OrdAlt src x pres₁-ev
ordSC-e⇒p₁ {x} ¬x-pres₁ ((refl , x-rw) ⨾[ x ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ y ]⨾ po[ye]) =
  let ¬y-pres₁ = λ{y≡p₁ → disjoint-f/r _ (f₌⇒f y-f , subst EvR (≡-sym y≡p₁) pres₁-r)}
      ¬y-pres₂ = λ{y≡p₂ → disjoint-f/mode (λ()) _ (y-f , subst (EvF₌ RM) (≡-sym y≡p₂) pres₂-f₌)}
      po[yp₁] = unsplitʳ-p₁p₂ ¬y-pres₁ ¬y-pres₂ po[ye]
  in ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[yp₁] ⨾[ _ ]⨾ (refl , r⇒rw pres₁-r))


ordʳ-e⇒p : {x : Event LabelLIMM}
  → x ≢ pres₁-ev
  → OrdAlt src x src-elim-ev
  → OrdAlt src x pres₁-ev
ordʳ-e⇒p ¬x-pres₁ (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw)))
  with unsplit-po-triʳ src-wf po[xe] po[p₁e]
... | tri<  po[xp₁] x≢p  ¬po[p₁x] = ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , r⇒rw pres₁-r))
... | tri≈ ¬po[xp₁] refl ¬po[p₁x] = ⊥-elim (disjoint-r/init _ (pres₁-r , x-init))
... | tri> ¬po[xp₁] x≢p   po[p₁x] =
  let p₁-init = po-init-first src-wf po[p₁x] x-init
  in ⊥-elim (disjoint-r/init _ (pres₁-r , p₁-init))
ordʳ-e⇒p {x} ¬x-pres₁ (ord-rm ((refl , x-r) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ y ]⨾ po[ye] ⨾[ _ ]⨾ (refl , e-rw)))
  with r/tag x-r
... | inj₂ x-rₐ =
  let po[xe] = po-trans src-wf po[xy] po[ye]
      po[xp₁] = poʳ-e⇒p (r⇒rw x-r) ¬x-pres₁ po[xe]
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , r⇒rw pres₁-r))
... | inj₁ x-rᵣ =
  ordRM-e⇒p₁ ¬x-pres₁ ((refl , x-rᵣ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[ye])
ordʳ-e⇒p ¬x-pres₁ (ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[ye] ⨾[ _ ]⨾ (refl , e-rw))) =
  ordSC-e⇒p₁ ¬x-pres₁ ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-f) ⨾[ _ ]⨾ po[ye])
ordʳ-e⇒p ¬x-pres₁ (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e∈rmwˡ))) =
  ⊥-elim (disjoint-rₜ _ (src-elim-rₜ , rmwˡ-r src-wf e∈rmwˡ))
ordʳ-e⇒p ¬x-pres₁ (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬x-pres₁ = λ{x≡p₁ → disjoint-r/w _ (pres₁-r , subst EvW x≡p₁ (wₜ⇒w (rmwʳ-w src-wf x∈rmwʳ)))}
      ¬x-pres₂ = λ{x≡p₂ → disjoint-f/w _ (pres₂-f , subst EvW x≡p₂ (wₜ⇒w (rmwʳ-w src-wf x∈rmwʳ)))}
      po[xp₁] = unsplitʳ-p₁p₂ ¬x-pres₁ ¬x-pres₂ po[xe]
  in ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , r⇒rw pres₁-r))
ordʳ-e⇒p ¬x-pres₁ (ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-wₐ))) =
  ⊥-elim (disjoint-r/w _ (src-elim-r , wₜ⇒w e-wₐ))
ordʳ-e⇒p ¬x-pres₁ (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xe] ⨾[ _ ]⨾ (refl , e-rw))) =
  let ¬x-pres₁ = λ{x≡p₁ → disjoint-rₜ _ (pres₁-rₜ , subst EvRₐ x≡p₁ x-rₐ)}
      ¬x-pres₂ = λ{x≡p₂ → disjoint-f/r _ (pres₂-f , subst EvR x≡p₂ (rₜ⇒r x-rₐ))}
      po[xp₁] = unsplitʳ-p₁p₂ ¬x-pres₁ ¬x-pres₂ po[xe]
  in ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xp₁] ⨾[ _ ]⨾ (refl , r⇒rw pres₁-r))
-- impssible
ordʳ-e⇒p ¬x-pres₁ (ord-ww ww[xe]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ord-predʳ src ww[xe]))


ordˡ-e⇒p : {y : Event LabelLIMM}
  → OrdAlt src src-elim-ev y
  → OrdAlt src pres₁-ev y
ordˡ-e⇒p ord[ey] = ordˡ+rᵣ src-wf po[p₁e] ord[ey] src-elim-rₜ pres₁-rₜ


¬poˡ-e⇒p : {y : Event LabelLIMM}
  → y ≢ pres₂-ev
  → y ≢ src-elim-ev
  → ¬ po src src-elim-ev y → ¬ po src pres₁-ev y
¬poˡ-e⇒p ¬y-pres₂ ¬y-elim ¬po[ey] po[p₁y] = ¬po[ey] (unsplitˡ-p₁p₂ ¬y-pres₂ ¬y-elim po[p₁y])


¬poʳ-e⇒p : {x : Event LabelLIMM}
  → ¬ po src x src-elim-ev
  → ¬ po src x pres₁-ev
¬poʳ-e⇒p ¬po[xe] po[xp₁] = ¬po[xe] (po-trans src-wf po[xp₁] po[p₁e])


freˡ-e⇒p : {y : Event LabelLIMM} → fre src src-elim-ev y → fre src pres₁-ev y
freˡ-e⇒p (fr[ey] , ¬po[ey]) =
  let ¬y-pres₂ = λ{refl → disjoint-f/w _ (pres₂-f , ×₂-applyʳ (fr-r×w src-wf) fr[ey])}
      ¬y-elim = λ{refl → fr-irreflexive src-wf refl fr[ey]}
  in frˡ-e⇒p fr[ey] , ¬poˡ-e⇒p ¬y-pres₂ ¬y-elim ¬po[ey]


rfeʳ-e⇒p : {x : Event LabelLIMM} → rfe src x src-elim-ev → rfe src x pres₁-ev
rfeʳ-e⇒p (rf[xe] , ¬po[xe]) = rfʳ-e⇒p rf[xe] , ¬poʳ-e⇒p ¬po[xe]


ghbiʳ-e⇒p : {x : Event LabelLIMM}
  → x ≢ pres₁-ev
  → GhbiAlt src x src-elim-ev
  → GhbiAlt src x pres₁-ev
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-ord ord[xe]) = ghbi-ord (ordʳ-e⇒p ¬x-pres₁ ord[xe])
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-rfe rfe[xe]) = ghbi-rfe (rfeʳ-e⇒p rfe[xe])
-- impossible cases
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-coe coe[xe]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (coe-w×w src-wf) coe[xe]))
ghbiʳ-e⇒p ¬x-pres₁ (ghbi-fre fre[xe]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyʳ (fre-r×w src-wf) fre[xe]))


ghbiˡ-e⇒p : {y : Event LabelLIMM}
  → GhbiAlt src src-elim-ev y
  → GhbiAlt src pres₁-ev y
ghbiˡ-e⇒p (ghbi-ord ord[ey]) = ghbi-ord (ordˡ-e⇒p ord[ey])
ghbiˡ-e⇒p (ghbi-fre fre[ey]) = ghbi-fre (freˡ-e⇒p fre[ey])
-- impossible cases
ghbiˡ-e⇒p (ghbi-rfe rfe[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (rfe-w×r src-wf) rfe[ey]))
ghbiˡ-e⇒p (ghbi-coe coe[ey]) = ⊥-elim (disjoint-r/w _ (src-elim-r , ×₂-applyˡ (coe-w×w src-wf) coe[ey]))


¬pres₁-elim : pres₁-ev ≢ src-elim-ev
¬pres₁-elim p₁≡e = po-irreflexive src-wf p₁≡e po[p₁e]


cycleₙ-detour :
  ∀ {x y : Event LabelLIMM}
  → GhbiAlt src src-elim-ev x
  → TransClosure GhbiAltDetour x y
  → GhbiAlt src y src-elim-ev
  → ∃[ z ] TransClosure GhbiAltDetour z z
cycleₙ-detour {x} {y} ghbi[ex] ghbi⁺[xy] ghbi[ye]
  with ev-eq-dec y pres₁-ev
... | yes refl =
  let ghbi[p₁x] = ghbiˡ-e⇒p ghbi[ex]
      ¬x-elim = ⁺-lift-predˡ (proj₁ ∘ proj₂) ghbi⁺[xy]
  in _ , (ghbi[p₁x] , ¬pres₁-elim , ¬x-elim) ∷ ghbi⁺[xy]
... | no ¬y-pres₁ =
  let ghbi[p₁x] = ghbiˡ-e⇒p ghbi[ex]
      ghbi[yp₁] = ghbiʳ-e⇒p ¬y-pres₁ ghbi[ye]
      ¬x-elim = ⁺-lift-predˡ (proj₁ ∘ proj₂) ghbi⁺[xy]
      ¬y-elim = ⁺-lift-predʳ (proj₂ ∘ proj₂) ghbi⁺[xy]
  in _ , (ghbi[yp₁] , ¬y-elim , ¬pres₁-elim) ∷ (ghbi[p₁x] , ¬pres₁-elim , ¬x-elim) ∷ ghbi⁺[xy]


ghb-detour : ∀ {x : Event LabelLIMM}
  → TransClosure (GhbiAlt src) x x
  → ∃[ z ] TransClosure GhbiAltDetour z z
ghb-detour {x} ghbi⁺[xx] with divert-cycle ghbi⁺[xx] (λ{x → ev-eq-dec x src-elim-ev})
... | inj₁ (cycle₁ ghbi[xx]) =
  ⊥-elim (¬ghbi-cycle₁ src-wf ghbi[xx])
... | inj₁ (cycle₂ ¬elim-x ghbi[ex] ghbi[xe]) =
  ⊥-elim (¬ghbi-cycle₂ src-wf src-ax-coherence ghbi[ex] ghbi[xe])
... | inj₁ (cycleₙ ghbi[ex] ghbid⁺[xy] ghbi[ye]) =
  cycleₙ-detour ghbi[ex] ghbid⁺[xy] ghbi[ye]
... | inj₂ ghbid⁺[xx] = (_ , ghbid⁺[xx])


ghbi[⇒] : Rel[⇒] GhbiAltDetour (GhbiAlt dst)
ghbi[⇒] x∈src y∈src (ghbi-ord ord[xy] , ¬elim-x , ¬elim-y) = ghbi-ord (ord[⇒] ¬elim-x ¬elim-y x∈src y∈src ord[xy])
ghbi[⇒] x∈src y∈src (ghbi-rfe rfe[xy] , ¬elim-x , ¬elim-y) = ghbi-rfe (rfe[⇒] ¬elim-x ¬elim-y x∈src y∈src rfe[xy])
ghbi[⇒] x∈src y∈src (ghbi-coe coe[xy] , ¬elim-x , ¬elim-y) = ghbi-coe (coe[⇒] ¬elim-x ¬elim-y x∈src y∈src coe[xy])
ghbi[⇒] x∈src y∈src (ghbi-fre fre[xy] , ¬elim-x , ¬elim-y) = ghbi-fre (fre[⇒] ¬elim-x x∈src y∈src fre[xy])

ghbidˡ∈src : {x y : Event LabelLIMM} → GhbiAltDetour x y → x ∈ events src
ghbidˡ∈src (ghbi[xy] , _ , _) = GhbiAltˡ∈ex src-wf ghbi[xy]

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
