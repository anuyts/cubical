{-

This file contains a summary of the proofs that π₄(S³) ≡ ℤ/2ℤ

- The first proof "π₄S³≃ℤ/2ℤ" closely follows Brunerie's thesis.

- The second proof "π₄S³≃ℤ/2ℤ-direct" is much more direct and avoids
  all of the more advanced constructions in chapters 4-6 in Brunerie's
  thesis.

- The third proof "π₄S³≃ℤ/2ℤ-computation" uses ideas from the direct
  proof to define an alternative Brunerie number which computes to -2
  in a few seconds and the main result is hence obtained by computation
  as conjectured on page 85 of Brunerie's thesis.

The --experimental-lossy-unification flag is used to speed up type checking.
The file still type checks without it, but it's a lot slower (about 10 times).

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.Pi4S3.Summary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat.Base
open import Cubical.Data.Int.Base
open import Cubical.Data.Sigma.Base

open import Cubical.HITs.Sn
open import Cubical.HITs.SetTruncation

open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.HopfInvariant.Homomorphism
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.HopfInvariant.Brunerie
open import Cubical.Homotopy.Whitehead
open import Cubical.Homotopy.Group.Base hiding (π)
open import Cubical.Homotopy.Group.Pi3S2
open import Cubical.Homotopy.Group.Pi4S3.BrunerieNumber
open import Cubical.Homotopy.Group.Pi4S3.DirectProof as DirectProof

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.ZAction


-- Homotopy groups (shifted version of π'Gr to get nicer numbering)
π : ℕ → Pointed₀ → Group₀
π n X = π'Gr (predℕ n) X


-- Nicer notation for the spheres (as pointed types)
𝕊² 𝕊³ : Pointed₀
𝕊² = S₊∙ 2
𝕊³ = S₊∙ 3


-- The Brunerie number; defined in Cubical.Homotopy.Group.Pi4S3.BrunerieNumber
-- as "abs (HopfInvariant-π' 0 ([ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]×))"
β : ℕ
β = Brunerie


-- The connection to π₄(S³) is then also proved in the BrunerieNumber
-- file following Corollary 3.4.5 in Guillaume Brunerie's PhD thesis.
βSpec : GroupEquiv (π 4 𝕊³) (ℤGroup/ β)
βSpec = BrunerieIso


-- Ideally one could prove that β is 2 by normalization, but this does
-- not seem to terminate before we run out of memory. To try normalize
-- this use "C-u C-c C-n β≡2" (which normalizes the term, ignoring
-- abstract's). So instead we prove this by hand as in the second half
-- of Guillaume's thesis.
β≡2 : β ≡ 2
β≡2 = Brunerie≡2


-- This involves a lot of theory, for example that π₃(S²) ≃ ℤGroup where
-- the underlying map is induced by the Hopf invariant (which involves
-- the cup product on cohomology).
_ : GroupEquiv (π 3 𝕊²) ℤGroup
_ = hopfInvariantEquiv

-- Which is a consequence of the fact that π₃(S²) is generated by the
-- Hopf map.
_ : gen₁-by (π 3 𝕊²) ∣ HopfMap ∣₂
_ = π₂S³-gen-by-HopfMap

-- etc. For more details see the proof of "Brunerie≡2".


-- Combining all of this gives us the desired equivalence of groups:
π₄S³≃ℤ/2ℤ : GroupEquiv (π 4 𝕊³) (ℤGroup/ 2)
π₄S³≃ℤ/2ℤ = subst (GroupEquiv (π 4 𝕊³)) (cong ℤGroup/_ β≡2) βSpec


-- By the SIP this induces an equality of groups:
π₄S³≡ℤ/2ℤ : π 4 𝕊³ ≡ ℤGroup/ 2
π₄S³≡ℤ/2ℤ = GroupPath _ _ .fst π₄S³≃ℤ/2ℤ


-- As a sanity check we also establish the equality with Bool:
π₄S³≡Bool : π 4 𝕊³ ≡ BoolGroup
π₄S³≡Bool = π₄S³≡ℤ/2ℤ ∙ GroupPath _ _ .fst (GroupIso→GroupEquiv ℤGroup/2≅Bool)


-- We also have a much more direct proof in Cubical.Homotopy.Group.Pi4S3.DirectProof,
-- not relying on any of the more advanced constructions in chapters
-- 4-6 in Brunerie's thesis (but still using chapters 1-3 for the
-- construction). For details see the header of that file.

π₄S³≃ℤ/2ℤ-direct : GroupEquiv (π 4 𝕊³) (ℤGroup/ 2)
π₄S³≃ℤ/2ℤ-direct = DirectProof.BrunerieGroupEquiv


-- This direct proof allows us to define a much simplified version of
-- the Brunerie number:
β' : ℤ
β' = fst DirectProof.computer η₃'

-- This number computes definitionally to -2 in a few seconds!
β'≡-2 : β' ≡ -2
β'≡-2 = refl

-- As a sanity check we have proved (commented as typechecking is quite slow):
-- β'Spec : GroupEquiv (π 4 𝕊³) (ℤGroup/ abs β')
-- β'Spec = DirectProof.BrunerieGroupEquiv'

-- Combining all of this gives us the desired equivalence of groups by
-- computation as conjectured in Brunerie's thesis:
π₄S³≃ℤ/2ℤ-computation : GroupEquiv (π 4 𝕊³) (ℤGroup/ 2)
π₄S³≃ℤ/2ℤ-computation = DirectProof.BrunerieGroupEquiv''
