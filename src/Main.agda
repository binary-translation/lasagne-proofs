{-# OPTIONS --safe #-}


module Main where


--
-- + Proof intuition
--
-- All proofs follow a similar structure. We map a /source program/ Pₛ to a
-- /target program/ Pₜ . So we have:
--
-- > Pₛ  == maps to ==>  Pₜ
--
-- Of course, Pₜ needs to be /correct/. That is, it should behave similarly to Pₛ.
--
-- When Pₛ is a /concurrent program/, it can display many different behaviors,
-- which depend on thread-interleaving and CPU intricacies, such as instruction
-- reordering. So, we need to ensure Pₜ is /correct for all possible behaviors/.
-- That is:
--
-- " Every behavior of Pₜ must be justified by a corresponding behavior of Pₛ "
--
-- We thus model individual executions, which we denote by Xₛ and Xₜ,
-- for Pₛ and Pₜ, respectively. Thus we get:
--
-- > Xₛ == justifies ==> Xₜ
-- > 
-- > ↑                   ↑
-- >
-- > Pₛ === maps to ===> Pₜ
--
-- So, for /every execution/ Xₜ of Pₜ, we need to find a /corresponding execution/
-- Xₛ of Pₛ. If that is possible, the mapping is /correct/. Intuitively:
--
-- > ∀ Xₜ . { is-ok(Xₜ) → ∃ Xₛ . ( is-ok(Xₛ)  ∧  behavior(Xₛ) ≡ behavior(Xₜ) ) }
--
--
--
-- + Proof specifics
--
-- In the proofs, we only model the executions. We /specify/ constraints on the target
-- execution Xₜ:
--
-- * /Events follow syntax/ - For instance, if from the mapping we know every `LD`
--   /instruction/ is followed by a `F_RM` /instruction/, then in the execution we
--   know every Read /event/ is followed by a F_RM /event/.
--
-- * /Xₜ is wellformed/ - Wellformedness declares an execution "makes sense". That is,
--   for instance, every Read event reads from exactly one Write event. Only
--   executions that "make sense" can actually be observed from Pₜ.
--
-- * /Xₜ is consistent/ - Consistency declares that a behavior is observable
--   within a particular architecture's memory model. That is, the execution must
--   satisfy some architecture-specific constraints, which restrict the observable
--   behavior of Pₜ.
--
-- Note that we are /given/ such an execution Xₜ, for which we /construct/ a
-- corresponding execution Xₛ. We then demonstrate:
--
-- * /Xₛ is wellformed/ - We demonstrate Xₛ also "makes sense".
--
-- * /Xₛ is consistent/ - We demonstrate Xₛ can be observed in the source
--   architecture.
--
-- * /Xₛ "maps to" Xₜ/ - We demonstrate that the events in Xₛ map to the
--   event in Xₜ, following the syntactic mapping from Pₛ to Pₜ.
--
-- * /Xₛ "behaves like" Xₜ/ - We demonstrate that, upon termination, the state of
--   memory is identical for Xₛ and Xₜ.
--
-- And that is it. If such an execution Xₛ of Pₛ exists for every execution Xₜ of
-- Pₜ, then the corresponding mapping is correct. All the proofs follow that
-- structure.
--


-- # Architecture specifications

open import Arch.General.Execution
open import Arch.X86
open import Arch.Armv8
open import Arch.LIMM


-- # Architecture mapping proofs

-- ## x86 ⇒ LIMM
open import MapX86toLIMM              -- specification
open import Proof.Mapping.X86toLIMM   -- proof
-- ## LIMM ⇒ Armv8
open import MapLIMMtoArmv8            -- specification
open import Proof.Mapping.LIMMtoArmv8 -- proof

-- ## Armv8 ⇒ LIMM
open import MapArmv8toLIMM            -- specification
open import Proof.Mapping.Armv8toLIMM -- proof
-- ## LIMM ⇒ x86
open import MapLIMMtoX86              -- specification
open import Proof.Mapping.LIMMtoX86   -- proof


-- # Transformations on LIMM

-- ## RAR: Read-after-Read
open import TransformRAR           -- specification
open import Proof.Elimination.RAR  -- proof

-- ## WAW: Write-after-Write
open import TransformWAW           -- specification
open import Proof.Elimination.WAW  -- proof

-- ## RAW: Read-after-Write
open import TransformRAW           -- specification
open import Proof.Elimination.RAW  -- proof

-- ## FRAR: Read-after-Read with Fence
open import TransformFRAR          -- specification
open import Proof.Elimination.FRAR -- proof

-- ## FWAW: Write-after-Write with Fence
open import TransformFWAW          -- specification
open import Proof.Elimination.FWAW -- proof

-- ## FRAW: Read-after-Write with Fence
open import TransformFRAW          -- specification
open import Proof.Elimination.FRAW -- proof


-- # Reorderings on LIMM

-- ## Reordering:  a ∘ b  →  b ∘ a  (for some a,b)
open import TransformReorder      -- specification
open import Proof.Reorder.Single  -- proof

-- ## Reordering:  (a ∘ b) ∘ c  →  c ∘ (a ∘ b)  (for some a,b,c)
open import TransformReorder21       -- specification
open import Proof.Reorder.Reorder21  -- proof

-- ## Reordering:  a ∘ (b ∘ c)  →  (b ∘ c) ∘ a  (for some a,b,c)
open import TransformReorder12       -- specification
open import Proof.Reorder.Reorder12  -- proof
