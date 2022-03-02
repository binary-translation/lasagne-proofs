{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution)
open import Arch.LIMM using (LabelLIMM)
open import TransformFWAW using (FWAW-Restricted)


module Proof.Elimination.FWAW.WellFormed
  (dst : Execution LabelLIMM)
  (dst-ok : FWAW-Restricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level; _⊔_)
open import Function using (_∘_; flip)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (_∈_)
open import Relation.Binary using (Rel; Transitive; Tri; Trichotomous; tri<; tri≈; tri>)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architecture Specification
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.LIMM as LIMM
-- Local imports: Proof Components
import Proof.Framework LabelLIMM dst (FWAW-Restricted.wf dst-ok) as Ψ
import Proof.Elimination.Framework dst (FWAW-Restricted.wf dst-ok) as Δ
open import Proof.Elimination.FWAW.Execution dst dst-ok as WAW-Ex


-- General Proof Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Elimination Proof Framework
open Δ.Definitions δ
open Δ.WellFormed δ
-- Other
open Ex.Execution
open Ex.WellFormed
open TransformFWAW.Extra dst-ok
open FWAW-Restricted dst-ok
open WAW-Ex.Extra


src-rf-w×r : rf src ⊆₂ EvW ×₂ EvR
src-rf-w×r = ⊆: lemma
  where
  lemma : rf src ⊆₂' EvW ×₂ EvR
  lemma _ _ rf[xy] = src-rfˡ-w rf[xy] , src-rfʳ-r rf[xy]


src-co-w×w : co src ⊆₂ EvW ×₂ EvW
src-co-w×w = ⊆: lemma
  where
  lemma : co src ⊆₂' EvW ×₂ EvW
  lemma _ _ co[xy] = src-coˡ-w co[xy] , src-coʳ-w co[xy]


src-co-init-first : ⊤-Precedes-⊥ EvInit (co src)
src-co-init-first (co-dst (dst-x , dst-y , co[xy] , refl , refl)) y-init =
  let x∈src = events[⇐] (coˡ∈ex dst-wf co[xy])
      y∈src = events[⇐] (coʳ∈ex dst-wf co[xy])
      dst-y-init = Init[⇒] y∈src y-init
      dst-x-init = co-init-first dst-wf co[xy] dst-y-init
  in Init[⇐$] x∈src dst-x-init
-- Impossible cases
src-co-init-first (co-newˡ dst-co[py] refl refl) y-init =
  let pres-init = co-init-first dst-wf dst-co[py] (Init[$⇒] (coʳ∈ex dst-wf dst-co[py]) y-init)
  in ⊥-elim (disjoint-init/rwₙₜ _ (pres-init , wₙₜ⇒rwₙₜ pres₂-wₙᵣ))
src-co-init-first (co-newʳ dst-co[xp] refl refl) x-init =
  let elim-init = Init[$⇒] elim∈ex x-init
  in ⊥-elim (disjoint-skip/init _ (elim-ev-skip , elim-init))
src-co-init-first (co-ep refl refl) pres-init =
  ⊥-elim (disjoint-init/rwₙₜ _ (Init[$⇒] pres₂∈ex pres-init , wₙₜ⇒rwₙₜ pres₂-wₙᵣ))


src-co-trans : Transitive (co src)
-- co x y → co y z → co x z
src-co-trans (co-dst (_ , _ , co[xy] , refl , refl)) (co-dst (_ , _ , co[yz] , τ , refl))
  with ev[$⇒]eq (coʳ∈ex dst-wf co[xy]) (coˡ∈ex dst-wf co[yz]) τ
... | refl = co-dst (_ , _ , co-trans dst-wf co[xy] co[yz] , refl , refl)
-- co x y → co y e → co x e
src-co-trans (co-dst (_ , _ , co[xy] , refl , refl)) (co-newʳ co[yp] τ refl)
  with ev[$⇒]eq (coʳ∈ex dst-wf co[xy]) (coˡ∈ex dst-wf co[yp]) τ
... | refl =
  co-newʳ (co-trans dst-wf co[xy] co[yp]) refl refl
-- co p x → co x y → co p y
src-co-trans (co-newˡ co[px] refl refl) (co-dst (_ , _ , co[xy] , τ , refl))
  with ev[$⇒]eq (coʳ∈ex dst-wf co[px]) (coˡ∈ex dst-wf co[xy]) τ
... | refl = co-newˡ (co-trans dst-wf co[px] co[xy]) refl refl
src-co-trans (co-newʳ co[xp] refl refl) (co-newˡ co[py] refl refl) =
  co-dst (_ , _ , co-trans dst-wf co[xp] co[py] , refl , refl)
src-co-trans (co-newʳ co[xp] refl refl) (co-ep refl refl) =
  co-dst (_ , _ , co[xp] , refl , refl)
src-co-trans (co-ep refl refl) (co-dst (_ , _ , co[py] , τ , refl))
  with ev[$⇒]eq pres₂∈ex (coˡ∈ex dst-wf co[py]) τ
... | refl = co-newˡ co[py] refl refl
-- Impossible Cases
-- co x e → co e y → ⊥
src-co-trans (co-dst (_ , _ , co[xe] , refl , refl)) (co-newˡ co[py] τ refl)
  with ev[$⇒]eq (coʳ∈ex dst-wf co[xe]) elim∈ex τ
... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyʳ (co-w×w dst-wf) co[xe] , elim-ev-skip))
-- co x e → co e p → ⊥
src-co-trans (co-dst (_ , _ , co[xe] , refl , refl)) (co-ep τ refl)
  with ev[$⇒]eq (coʳ∈ex dst-wf co[xe]) elim∈ex τ
... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyʳ (co-w×w dst-wf) co[xe] , elim-ev-skip))
-- co p e → co p y → ⊥
src-co-trans (co-newˡ co[pe] refl refl) (co-newˡ dst-co[py] τ refl)
  with ev[$⇒]eq (coʳ∈ex dst-wf co[pe]) elim∈ex τ
... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyʳ (co-w×w dst-wf) co[pe] , elim-ev-skip))
-- co p y → co y p → ⊥
src-co-trans (co-newˡ co[py] refl refl) (co-newʳ co[yp] τ refl)
  with ev[$⇒]eq (coʳ∈ex dst-wf co[py]) (coˡ∈ex dst-wf co[yp]) τ
... | refl = ⊥-elim (co-irreflexive dst-wf refl (co-trans dst-wf co[py] co[yp]))
-- co p e → co e p → ⊥
src-co-trans (co-newˡ co[pe] refl refl) (co-ep τ refl)
  with ev[$⇒]eq (coʳ∈ex dst-wf co[pe]) elim∈ex τ
... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyʳ (co-w×w dst-wf) co[pe] , elim-ev-skip))
-- co x e → co e y → ⊥
src-co-trans (co-newʳ co[xe] refl refl) (co-dst (_ , _ , co[ez] , τ , refl))
  with ev[$⇒]eq elim∈ex (coˡ∈ex dst-wf co[ez]) τ
... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyˡ (co-w×w dst-wf) co[ez] , elim-ev-skip))
-- co x p → co e p → ⊥
src-co-trans (co-newʳ co[xp] refl refl) (co-newʳ co[ep] τ refl)
  with ev[$⇒]eq elim∈ex (coˡ∈ex dst-wf co[ep]) τ
... | refl = ⊥-elim (disjoint-w/skip _ (×₂-applyˡ (co-w×w dst-wf) co[ep] , elim-ev-skip))
-- co e p → co e y → ⊥
src-co-trans (co-ep refl refl) (co-newˡ co[ey] τ refl) =
  ⊥-elim (¬pres₂-elim (≡-trans src-pres₂-def τ))
-- co e p → co p p → ⊥
src-co-trans (co-ep refl refl) (co-newʳ co[pp] τ refl) =
  ⊥-elim (co-irreflexive dst-wf (≡-sym (ev[$⇒]eq pres₂∈ex (coˡ∈ex dst-wf co[pp]) τ)) co[pp])
src-co-trans (co-ep refl refl) (co-ep τ refl) =
  ⊥-elim (¬pres₂-elim (≡-trans src-pres₂-def τ))


unique-co-pred : (loc : Location) → UniquePred (EvW ∩₁ HasLoc loc ∩₁ events src)
unique-co-pred _ = ∩₁-unique-pred w-unique (∩₁-unique-pred has-loc-unique src-events-unique)

dst-unique-co-pred : (loc : Location) → UniquePred (EvW ∩₁ HasLoc loc ∩₁ events dst)
dst-unique-co-pred _ = ∩₁-unique-pred w-unique (∩₁-unique-pred has-loc-unique (events-unique dst-wf))

¬co[ee] : ¬ co src src-elim-ev src-elim-ev
¬co[ee] co[ee] =
  let co[pp] = coʳ-e⇒p (coˡ-e⇒p (≢-sym ¬pres₂-elim) co[ee])
      dst-co[pp] = co[⇒] ¬pres₂-elim ¬pres₂-elim pres₂∈src pres₂∈src co[pp]
  in co-irreflexive dst-wf refl dst-co[pp]


private
  -- Trichotomous w.r.t. a single element
  SemiTrichotomous : {a ℓ : Level} {A : Set a} → Rel A ℓ → A → Set (a ⊔ ℓ)
  SemiTrichotomous R x = ∀ y → Tri (R x y) (x ≡ y) (R y x)

  co-pred[⇒] : (loc : Location) → CPred[⇒] (EvW ∩₁ HasLoc loc ∩₁ events src) (EvW ∩₁ HasLoc loc ∩₁ events dst)
  co-pred[⇒] loc ¬x-elim x∈src (x-w , x-loc , _) =
    (W[⇒] ¬x-elim x∈src x-w , loc[⇒] ¬x-elim x∈src x-loc , events[⇒] x∈src)

  pˢ-sloc-pᵗ : SameLoc src-pres₂-ev pres₂-ev
  pˢ-sloc-pᵗ = same-loc src-pres₂-has-loc pres₂-has-loc

  loc-eˢ⇒pᵗ : (loc : Location) → HasLoc loc src-elim-ev → HasLoc loc pres₂-ev
  loc-eˢ⇒pᵗ _ = subst-sloc (trans-same-loc ep₂-sloc pˢ-sloc-pᵗ)

  coˡ-p⇒e : {y : Event LabelLIMM} → co src src-pres₂-ev y → co src src-elim-ev y
  coˡ-p⇒e = src-co-trans (co-ep refl src-pres₂-def)

  ev[⇒]eq : {x y : Event LabelLIMM}
    → (x∈src : x ∈ events src) (y∈src : y ∈ events src)
    → x ≡ y
    → ev[⇒] x∈src ≡ ev[⇒] y∈src
  ev[⇒]eq x∈src y∈src refl = cong ev[⇒] (src-events-unique _ x∈src y∈src)

  dst-pres₂-def : pres₂-ev ≡ ev[⇒] pres₂∈src
  dst-pres₂-def = ev[⇒]eq (events[⇐] pres₂∈ex) pres₂∈src (≡-sym src-pres₂-def)

  src-co-stri :
      (loc : Location)
    → (e-w : EvW src-elim-ev)
    → (e-loc : HasLoc loc src-elim-ev)
    → (e∈src : src-elim-ev ∈ events src)
    → SemiTrichotomous
        (filter-rel (EvW ∩₁ HasLoc loc ∩₁ events src) (co src))
        (with-pred src-elim-ev (e-w , e-loc , e∈src))
  src-co-stri loc e-w e-loc e∈src (with-pred y (y-w , y-loc , y∈src)) with ev-eq-dec y src-elim-ev
  ... | yes refl = tri≈ ¬co[ee] (with-pred-unique (unique-co-pred loc) refl _ _) ¬co[ee]
  ... | no ¬y-elim
    with co-tri dst-wf elim-loc
           (with-pred pres₂-ev (pres₂-w , pres₂-has-loc , pres₂∈ex))
           (with-pred (ev[⇒] y∈src) (co-pred[⇒] elim-loc ¬y-elim y∈src (y-w , subst-sloc (same-loc e-loc y-loc) src-elim-has-loc , y∈src)))
  ... | tri<  co[py] p≢y ¬co[yp] =
    let q : src-pres₂-ev ∈ events src
        q = pres₂∈src
    in
    tri<
      (coˡ-p⇒e (subst-rel (co src) (≡-sym src-pres₂-def) (≡-sym (ev[⇒⇐] y∈src)) (co[⇐] pres₂∈ex (events[⇒] y∈src) co[py])))
      (λ{refl → ¬y-elim refl})
      (λ{co[ye] → ¬co[yp] (subst-rel (co dst) refl (ev[⇒]eq pres₂∈src (events[⇐] pres₂∈ex) src-pres₂-def) (co[⇒] ¬y-elim ¬pres₂-elim y∈src pres₂∈src (coʳ-e⇒p co[ye])))})
      -- (co[⇒] ¬y-elim ? y∈src pres₂∈src (coʳ-e⇒p co[ye]))})
  ... | tri≈ ¬co[py] p≡y ¬co[yp] =
    let src-p≡y : src-pres₂-ev ≡ y
        src-p≡y = ≡-trans src-pres₂-def (ev[⇐$]eq (events[⇐] pres₂∈ex) y∈src (with-pred-≡ p≡y))
    in
    tri<
      (co-ep refl (≡-trans (≡-sym src-p≡y) src-pres₂-def))
      (¬y-elim ∘ ≡-sym ∘ with-pred-≡)
      (¬co[yp] ∘ subst-rel (co dst) refl (≡-sym dst-pres₂-def) ∘ co[⇒] ¬y-elim ¬pres₂-elim y∈src pres₂∈src ∘ coʳ-e⇒p)
  ... | tri> ¬co[py] p≢y  co[yp] =
    tri>
      (λ{co[ey] →
        let ¬y-pres = λ{refl → p≢y (with-pred-unique (dst-unique-co-pred _) (≡-trans dst-pres₂-def (ev[⇒]eq pres₂∈src y∈src refl)) _ _)}
        in ¬co[py] (subst-rel (co dst) (≡-sym dst-pres₂-def) refl (co[⇒] ¬pres₂-elim ¬y-elim pres₂∈src y∈src (coˡ-e⇒p ¬y-pres co[ey])))})
      (¬y-elim ∘ ≡-sym ∘ with-pred-≡)
      (co-newʳ co[yp] (ev[⇒⇐] y∈src) refl)

  tri-flip-args : ∀ {a ℓ : Level} {A : Set a} (R : Rel A ℓ) {x y : A}
    → Tri (R x y) (x ≡ y) (R y x) → Tri (R y x) (y ≡ x) (R x y)
  tri-flip-args _ (tri<  a ¬b ¬c) = tri> ¬c (≢-sym ¬b) a
  tri-flip-args _ (tri≈ ¬a  b ¬c) = tri≈ ¬c (≡-sym b) ¬a
  tri-flip-args _ (tri> ¬a ¬b  c) = tri< c (≢-sym ¬b) ¬a


src-co-tri : (loc : Location) → Trichotomous _≡_ (filter-rel (EvW ∩₁ HasLoc loc ∩₁ events src) (co src))
src-co-tri loc (with-pred x xp@(x-w , x-loc , x∈src)) (with-pred y yp@(y-w , y-loc , y∈src))
  with ev-eq-dec x src-elim-ev | ev-eq-dec y src-elim-ev
... | yes refl   | yes refl   =
  tri≈ ¬co[ee] (with-pred-unique (unique-co-pred loc) refl _ _) ¬co[ee]
... | yes refl   | no ¬y-elim = src-co-stri loc x-w x-loc x∈src (with-pred y (y-w , y-loc , y∈src))
... | no ¬x-elim | yes refl   =
  tri-flip-args (filter-rel (EvW ∩₁ HasLoc loc ∩₁ events src) (co src)) (src-co-stri loc y-w y-loc y∈src (with-pred x (x-w , x-loc , x∈src)))
... | no ¬x-elim | no ¬y-elim
  with co-tri dst-wf loc (with-pred (ev[⇒] x∈src) (co-pred[⇒] loc ¬x-elim x∈src xp)) (with-pred (ev[⇒] y∈src) (co-pred[⇒] loc ¬y-elim y∈src yp))
... | tri<  co[xy] x≢y ¬co[yx] =
  tri<
    (co[⇐$] x∈src y∈src co[xy])
    (λ{refl → x≢y (with-pred-unique (dst-unique-co-pred loc) refl _ _)})
    (¬co[yx] ∘ co[⇒] ¬y-elim ¬x-elim y∈src x∈src)
... | tri≈ ¬co[xy] x≡y ¬co[yx] =
  let src-x≡y = ev[⇐$]eq x∈src y∈src (with-pred-≡ x≡y)
  in
  tri≈
    (¬co[xy] ∘ co[⇒] ¬x-elim ¬y-elim x∈src y∈src)
    (with-pred-unique (unique-co-pred loc) src-x≡y _ _)
    (¬co[yx] ∘ co[⇒] ¬y-elim ¬x-elim y∈src x∈src)
... | tri> ¬co[xy] x≢y  co[yx] =
  tri>
    (¬co[xy] ∘ co[⇒] ¬x-elim ¬y-elim x∈src y∈src)
    (λ{refl → x≢y (with-pred-unique (dst-unique-co-pred loc) refl _ _)})
    (co[⇐$] y∈src x∈src co[yx])


src-rf-elements : udr (rf src) ⊆₁ events src
src-rf-elements = ⊆: (λ _ → udr-rf∈src)


src-co-elements : udr (co src) ⊆₁ events src
src-co-elements = ⊆: (λ _ → udr-co∈src)


src-rf-sloc : rf src ⊆₂ SameLoc
src-rf-sloc = ⊆: lemma
  where
  lemma : rf src ⊆₂' SameLoc
  lemma _ _ (_ , _ , dst-rf[xy] , refl , refl) =
    let x∈dst = rfˡ∈ex dst-wf dst-rf[xy]
        y∈dst = rfʳ∈ex dst-wf dst-rf[xy]
        xy-sloc = ⊆₂-apply (rf-sloc dst-wf) dst-rf[xy]
    in sloc[⇐$] (events[⇐] x∈dst) (events[⇐] y∈dst) xy-sloc


private
  sloc[⇐] : Rel[⇐]² SameLoc
  sloc[⇐] = [⇐$]→₂[⇐] sloc[⇐$]


slocˢᵗ : SameLoc src-pres₂-ev (ev[⇐] pres₂∈ex)
slocˢᵗ = same-loc src-pres₂-has-loc (loc[⇐] pres₂∈ex pres₂-has-loc)

src-co-sloc : co src ⊆₂ SameLoc
src-co-sloc = ⊆: lemma
  where
  lemma : co src ⊆₂' SameLoc
  lemma x y (co-dst (_ , _ , co[xy] , refl , refl)) =
    let x∈dst = coˡ∈ex dst-wf co[xy]
        y∈dst = coʳ∈ex dst-wf co[xy]
    in sloc[⇐] x∈dst y∈dst (⊆₂-apply (co-sloc dst-wf) co[xy])
  lemma e y (co-newˡ dst-co[py] refl refl) =
    let y∈dst = coʳ∈ex dst-wf dst-co[py]
        py-sloc = ⊆₂-apply (co-sloc dst-wf) dst-co[py]
    in trans-same-loc (trans-same-loc ep₂-sloc slocˢᵗ) (sloc[⇐] pres₂∈ex y∈dst py-sloc)
  lemma x e (co-newʳ dst-co[xp] refl refl) =
    let x∈dst = coˡ∈ex dst-wf dst-co[xp]
        xp-sloc = ⊆₂-apply (co-sloc dst-wf) dst-co[xp]
    in trans-same-loc (sloc[⇐] x∈dst pres₂∈ex xp-sloc) (trans-same-loc (sym-same-loc slocˢᵗ) (sym-same-loc ep₂-sloc))
  lemma x y (co-ep refl refl) = trans-same-loc ep₂-sloc slocˢᵗ


src-rf-sval : rf src ⊆₂ SameVal
src-rf-sval = ⊆: lemma
  where
  lemma : rf src ⊆₂' SameVal
  lemma _ _ (_ , _ , dst-rf[xy] , refl , refl) =
    let x∈dst = rfˡ∈ex dst-wf dst-rf[xy]
        y∈dst = rfʳ∈ex dst-wf dst-rf[xy]
        xy-sval = ⊆₂-apply (rf-sval dst-wf) dst-rf[xy]
    in sval[⇐$] (events[⇐] x∈dst) (events[⇐] y∈dst) xy-sval


src-wf-rf-≥1 : (EvR ∩₁ events src) ⊆₁ codom (rf src)
src-wf-rf-≥1 = ⊆: lemma
  where
  lemma : (EvR ∩₁ events src) ⊆₁' codom (rf src)
  lemma x (x-r , x∈src) =
    let ¬x-elim = λ{refl → disjoint-r/w _ (x-r , src-elim-w)}
        dst-x-r = R[⇒] ¬x-elim x∈src x-r
        x∈dst = events[⇒] x∈src
        (y , rf[yx]) = ⊆₁-apply (wf-rf-≥1 dst-wf) (dst-x-r , x∈dst)
        y∈dst = rfˡ∈ex dst-wf rf[yx]
    in ev[⇐] y∈dst , rf[⇐$] (events[⇐] y∈dst) x∈src rf[yx]


src-wf-rf-≤1 : Functional _≡_ (flip (rf src))
src-wf-rf-≤1 x y₁ y₂ rf[y₁x] rf[y₂x] =
  let x∈src = rfʳ∈src rf[y₁x]
      y₁∈src = rfˡ∈src rf[y₁x]
      y₂∈src = rfˡ∈src rf[y₂x]
      dst-rf[y₁x] = [$⇒]→₂[⇒] (rel[$⇒] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)) y₁∈src x∈src rf[y₁x]
      dst-rf[y₂x] = [$⇒]→₂[⇒] (rel[$⇒] (rfˡ∈ex dst-wf) (rfʳ∈ex dst-wf)) y₂∈src x∈src rf[y₂x]
      dst-y₁≡y₂ = wf-rf-≤1 dst-wf _ _ _ dst-rf[y₁x] dst-rf[y₂x]
  in ev[⇐$]eq y₁∈src y₂∈src dst-y₁≡y₂


src-wf : Ex.WellFormed src
src-wf =
  record
    { unique-ids     = src-unique-ids
    ; events-unique  = src-events-unique
    ; rmw-def        = src-rmw-def
    ; rmw-w          = src-rmw-w
    ; rf-w×r         = src-rf-w×r
    ; co-w×w         = src-co-w×w
    ; rmw-r×w        = src-rmw-r×w
    ; po-init-first  = src-po-init-first
    ; co-init-first  = src-co-init-first
    ; po-tri         = src-po-tri
    ; co-tri         = src-co-tri
    ; po-splittable  = src-po-splittable
    ; co-trans       = src-co-trans
    ; events-uid-dec = src-events-uid-dec
    ; rmwˡ-dec       = src-rmwˡ-dec
    ; po-elements    = src-po-elements
    ; rf-elements    = src-rf-elements
    ; co-elements    = src-co-elements
    ; po-stid        = src-po-stid
    ; rf-sloc        = src-rf-sloc
    ; co-sloc        = src-co-sloc
    ; rmw-sloc       = src-rmw-sloc
    ; rf-sval        = src-rf-sval
    ; wf-rf-≥1       = src-wf-rf-≥1
    ; wf-rf-≤1       = src-wf-rf-≤1
    ; wf-init-≥1     = src-wf-init-≥1
    ; wf-init-≤1     = src-wf-init-≤1
    }
