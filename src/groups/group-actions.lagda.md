---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.group-actions where

open import groups.concrete-groups public
open import the-circle.the-circle public

-- ref sec:gsets

module _
  {ℓ' ℓ : Level} (G : Concrete-Group ℓ') (A : UU ℓ)
  where
  
  action-Concrete-Group : UU (ℓ' ⊔ ℓ)
  action-Concrete-Group = classifying-type-Concrete-Group G → A

  object-action-Concrete-Group : action-Concrete-Group → A
  object-action-Concrete-Group X = X (shape-Concrete-Group G)

_-Set_ : {ℓ' : Level} (G : Concrete-Group ℓ') (ℓ : Level) → UU (ℓ' ⊔ lsuc ℓ)
G -Set ℓ = action-Concrete-Group G (UU-Set ℓ)

module _
  {ℓ' ℓ : Level} (G : Concrete-Group ℓ') (X : G -Set ℓ)
  where

  set-action-Concrete-Group : UU-Set ℓ
  set-action-Concrete-Group = X (shape-Concrete-Group G)

  type-action-Concrete-Group : UU ℓ
  type-action-Concrete-Group = type-Set set-action-Concrete-Group

  _·G_ :
    (g : type-Concrete-Group G) →
    type-action-Concrete-Group → type-action-Concrete-Group
  g ·G x = tr (λ y → type-Set (X y)) g x

module _
  {ℓ : Level} (G : Concrete-Group ℓ) 
  where 

  private shG = shape-Concrete-Group G
  private BG = classifying-type-Concrete-Group G

  generalized-principal-torsor-action-Concrete-Group : BG → G -Set ℓ
  generalized-principal-torsor-action-Concrete-Group = Id-BG-Set G

  -- ref def:principaltorsor
  principal-torsor-action-Concrete-Group : G -Set ℓ
  principal-torsor-action-Concrete-Group =
    generalized-principal-torsor-action-Concrete-Group shG

  private P = principal-torsor-action-Concrete-Group

  -- ref def:adjointrep
  adjoint-rep-action-Concrete-Group : G -Set ℓ
  adjoint-rep-action-Concrete-Group X = Id-BG-Set G X X
  
  Ad = adjoint-rep-action-Concrete-Group

  k = pr1 (ind-𝕊¹ (λ _ → BG))

  free-loop-from-adjoint-rep : Σ (BG) (λ z → type-Set (Ad z)) → (𝕊¹ → BG)
  free-loop-from-adjoint-rep (pair z l) =
    map-apply-universal-property-𝕊¹ z l

  -- is-transitive-group-action : UU-Prop ℓ 
  -- is-transitive-group-action = 
```
