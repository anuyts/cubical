{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.EilenbergMoore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Univalence

open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Adjoint

private
  variable
    ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} (monadM : Monad C) where

  M : Functor C C
  M = fst monadM

  --open Category
  private
    module C = Category C
  open Functor
  open NatTrans

  open IsMonad (snd monadM)

  record IsEMAlgebra (algA : Algebra M) : Type ℓC' where
    constructor proveEMAlgebra
    open Algebra algA
    field
      str-η : str C.∘ N-ob η carrier ≡ C.id
      str-μ : str C.∘ N-ob μ carrier ≡ str C.∘ F-hom M str

  open IsEMAlgebra

  isPropIsEMAlgebra : ∀ {algA} → isProp (IsEMAlgebra algA)
  isPropIsEMAlgebra {algA} isalg isalg' = cong₂ proveEMAlgebra
    (C.isSetHom _ _ (str-η isalg) (str-η isalg'))
    (C.isSetHom _ _ (str-μ isalg) (str-μ isalg'))

  EMAlgebra : Type (ℓ-max ℓC ℓC')
  EMAlgebra = Σ[ algA ∈ Algebra M ] IsEMAlgebra algA

  EMCategory : Category (ℓ-max ℓC ℓC') ℓC'
  EMCategory = FullSubcategory (AlgebrasCategory M) IsEMAlgebra

  ForgetEM : Functor EMCategory (AlgebrasCategory M)
  ForgetEM = FullInclusion (AlgebrasCategory M) IsEMAlgebra

  ForgetEMAlgebra : Functor EMCategory C
  ForgetEMAlgebra = funcComp (ForgetAlgebra M) ForgetEM

  open Algebra
  freeEMAlgebra : C.ob → EMAlgebra
  carrier (fst (freeEMAlgebra x)) = F-ob M x
  str (fst (freeEMAlgebra x)) = N-ob μ x
  str-η (snd (freeEMAlgebra x)) = lemma
    where lemma : N-ob η (F-ob M x) C.⋆ N-ob μ x ≡ C.id
          lemma = funExt⁻ (congP (λ i → N-ob) idl-μ) x
  str-μ (snd (freeEMAlgebra x)) = lemma
    where lemma : N-ob μ (F-ob M x) C.⋆ N-ob μ x ≡ F-hom M (N-ob μ x) C.⋆ N-ob μ x
          lemma = funExt⁻ (congP (λ i → N-ob) (symP-fromGoal assoc-μ)) x

  open AlgebraHom
  FreeEMAlgebra : Functor C EMCategory
  F-ob FreeEMAlgebra x = freeEMAlgebra x
  carrierHom (F-hom FreeEMAlgebra {x} {y} φ) = F-hom M φ
  strHom (F-hom FreeEMAlgebra {x} {y} φ) = sym (N-hom μ φ)
  F-id FreeEMAlgebra = AlgebraHom≡ M (F-id M)
  F-seq FreeEMAlgebra {x} {y} {z} φ ψ = AlgebraHom≡ M (F-seq M φ ψ)
