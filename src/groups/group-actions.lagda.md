---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.group-actions where

open import groups.concrete-groups public
open import the-circle.the-circle public

-- ref sec:gsets

group-actions : {ℓ ℓ' : Level} → (Concrete-Group ℓ) → UU ℓ' → UU (ℓ ⊔ ℓ')
group-actions G A = BG → A
  where
  BG = classifying-type-Concrete-Group G
 
group-actions-on-sets : {ℓ : Level} → (Concrete-Group ℓ) → UU (lsuc ℓ)
group-actions-on-sets {ℓ} G = group-actions G (UU-Set ℓ) 

_-Set : {ℓ : Level} → (Concrete-Group ℓ) → UU (lsuc ℓ)
G -Set = group-actions-on-sets G


module _
  {ℓ : Level} (G : Concrete-Group ℓ) 
  where 

  private shG = shape-Concrete-Group G
  private BG = classifying-type-Concrete-Group G


  -- ref def:principaltorsor
  principal-torsor-group-actions : G -Set
  principal-torsor-group-actions z =
    pair ( Id shG z)
         (
           prop-on-classifying-type-Concrete-Group
             G
             ( λ x → is-set-Prop (Id shG x))
             ( is-set-type-Concrete-Group G)
             z
         )

  Pr = principal-torsor-group-actions

  generalized-principal-torsor-group-actions : BG → G -Set
  generalized-principal-torsor-group-actions y z =
    pair ( Id y z)
         (
           prop-on-classifying-type-Concrete-Group
             G
             ( λ x → is-set-Prop (Id y x))
             ( prop-on-classifying-type-Concrete-Group
               G
               ( λ x' → is-set-Prop (Id x' shG))
               ( is-set-type-Concrete-Group G)
               y
             )
             z
         )

  -- would like to make a shortname P as in the book, but P is already
  -- taken in W-types. Should we use private for such common name?

  -- ref def:adjointrep
  adjoint-rep-group-actions : G -Set
  adjoint-rep-group-actions z =
    pair ( Id z z)
         ( prop-on-classifying-type-Concrete-Group
           G
           ( λ x → is-set-Prop (Id x x))
           ( is-set-type-Concrete-Group G)
           z
         )

  Ad = adjoint-rep-group-actions

  k = pr1 (ind-𝕊¹ (λ _ → BG))

  free-loop-from-adjoint-rep : Σ (BG) (λ z → type-Set (Ad z)) → (𝕊¹ → BG)
  free-loop-from-adjoint-rep (pair z l) =
    apply-universal-property-𝕊¹ z l

  -- is-transitive-group-action : UU-Prop ℓ 
  -- is-transitive-group-action = 
```
