{-# OPTIONS --safe #-}


module Main where

-- # Architecture mapping proofs
-- ## X86 ⇒ Armv8
open import Proof.Mapping.X86toLIMM
open import Proof.Mapping.LIMMtoArmv8
-- ## Armv8 ⇒ X86
open import Proof.Mapping.Armv8toLIMM
open import Proof.Mapping.LIMMtoX86


-- # Transformations on LIMM
open import Proof.Elimination.RAR  -- Read-after-Read
open import Proof.Elimination.WAW  -- Write-after-Write
open import Proof.Elimination.RAW  -- Read-after-Write
open import Proof.Elimination.FRAR -- Read-after-Read with Fence
open import Proof.Elimination.FWAW -- Write-after-Write with Fence
open import Proof.Elimination.FRAW -- Read-after-Write with Fence


-- # Reorderings on LIMM
open import Proof.Reorder.Single    -- a ∘ b        →  b ∘ a
open import Proof.Reorder.Reorder21 -- (a ∘ b) ∘ c  →  c ∘ (a ∘ b)
open import Proof.Reorder.Reorder12 -- a ∘ (b ∘ c)  →  (b ∘ c) ∘ a
