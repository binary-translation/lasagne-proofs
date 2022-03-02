{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformFRAW using (FRAW-Restricted)


module Proof.Elimination.FRAW.Behavior
  (dst : Execution LabelLIMM)
  (dst-ok : FRAW-Restricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_; yes; no)
-- Library imports
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
-- Local imports: Proof Components
open import Proof.Elimination.FRAW.Execution dst dst-ok as FRAW-Ex
open import Proof.Elimination.FRAW.WellFormed dst dst-ok as FRAW-Wf
import Proof.Framework LabelLIMM dst dst-wf as Ψ
import Proof.Elimination.Framework dst dst-wf as Δ


-- Proof Frameworks
open Ψ.Definitions ev[⇐]
open Δ.Definitions δ
-- Other
open FRAW-Ex.Extra
open Ex.Execution
open Ex.WellFormed


src-behavior : behavior src ⇔₂ behavior dst
src-behavior = ⇔: ⊆-proof ⊇-proof
  where
  ⊆-proof : behavior src ⊆₂' behavior dst
  ⊆-proof loc val (x , x∈src , x-w , x-val , x-loc , ¬∃z) =
    let ¬elim-x = elim-¬w x-w
    in
    ( ev[⇒] x∈src
    , events[⇒] x∈src
    , W[⇒] ¬elim-x x∈src x-w
    , val[⇒] ¬elim-x x∈src x-val
    , loc[⇒] ¬elim-x x∈src x-loc , ¬∃z'
    )
    where
    ¬∃z' : ¬ (∃[ z ] co dst (ev[⇒] x∈src) z)
    ¬∃z' (z , co[xz]) =
      let z∈dst = coʳ∈ex dst-wf co[xz]
      in ¬∃z (ev[⇐] z∈dst , co[⇐$] x∈src (events[⇐] z∈dst) co[xz])

  ⊇-proof : behavior dst ⊆₂' behavior src
  ⊇-proof loc val (x , x∈dst , x-w , x-val , x-loc , ¬∃z) = 
    ( ev[⇐] x∈dst
    , events[⇐] x∈dst
    , W[⇐] x∈dst x-w
    , val[⇐] x∈dst x-val
    , loc[⇐] x∈dst x-loc
    , ¬∃z'
    )
    where
    ¬∃z' : ¬ (∃[ z ] co src (ev[⇐] x∈dst) z)
    ¬∃z' (z , co[xz]) =
      let x∈src = events[⇐] x∈dst
          z∈src = coʳ∈src co[xz]
          ¬x-elim = elim-¬w (W[⇐] x∈dst x-w)
          ¬z-elim = elim-¬w (×₂-applyʳ (co-w×w src-wf) co[xz])
      in ¬∃z (ev[⇒] z∈src , co[⇒] ¬x-elim ¬z-elim x∈src z∈src co[xz])
