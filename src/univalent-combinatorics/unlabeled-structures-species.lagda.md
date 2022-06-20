---
title: Unlabeled structures of a species
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.unlabeled-structures-species where

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

## Idea

The type of unlabeled `F`-structures of order `n` of a species `F` is the type of sets `X` of size `n` equipped with an `F`-structure. Two unlabeled `F`-structures of order `n` are considered to be the same if the underlying sets are isomorphic and the `F`-structure of the first transports along this isomorphism to the `F`-structure of the second. It will automatically follow from the univalence axiom that the identity type of the type of unlabeled `F`-structures of order `n` captures this idea.

## Definitions

### Unlabeled structures of a species

```agda
unlabeled-structure-species :
  {l : Level} (F : species l) → ℕ → UU (lsuc lzero ⊔ l)
unlabeled-structure-species F n = Σ (UU-Fin n) (λ X → F (finite-type-UU-Fin X))

module _
  {l : Level} (F : species l) {k : ℕ} (X : unlabeled-structure-species F k)
  where

  type-of-cardinality-unlabeled-structure-species : UU-Fin k
  type-of-cardinality-unlabeled-structure-species = pr1 X

  type-unlabeled-structure-species : UU lzero
  type-unlabeled-structure-species =
    type-UU-Fin type-of-cardinality-unlabeled-structure-species

  has-cardinality-type-unlabeled-structure-species :
    has-cardinality k type-unlabeled-structure-species
  has-cardinality-type-unlabeled-structure-species =
    has-cardinality-type-UU-Fin type-of-cardinality-unlabeled-structure-species

  finite-type-unlabeled-structure-species : 𝔽
  finite-type-unlabeled-structure-species =
    finite-type-UU-Fin type-of-cardinality-unlabeled-structure-species

  structure-unlabeled-structure-species :
    F finite-type-unlabeled-structure-species
  structure-unlabeled-structure-species = pr2 X
```

### Equivalences of unlabeled structures of a speces

```agda
module _
  {l : Level} (F : species l)
  where
  
  equiv-unlabeled-structure-species :
    {k : ℕ} (X Y : unlabeled-structure-species F k) → UU {!!}
  equiv-unlabeled-structure-species X Y =
    Σ ( type-unlabeled-structure-species F X ≃
        type-unlabeled-structure-species F Y)
      {!!}
```
