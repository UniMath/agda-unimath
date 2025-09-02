# The minimum of finitely enumerable subsets of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.minimum-finitely-enumerable-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.lower-bounds-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.finitely-enumerable-subsets-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.infima-families-real-numbers
open import real-numbers.maximum-finitely-enumerable-subsets-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.subsets-real-numbers

open import univalent-combinatorics.finitely-enumerable-subtypes
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="finitely enumerable subset of Dedekind real numbers" Agda=min-inhabited-finitely-enumerable-subset-ℝ WD="minimum" WDID=Q10585806}}
of a
[finitely enumerable subset of the real numbers](real-numbers.finitely-enumerable-subsets-real-numbers.md)
is their [infimum](real-numbers.infima-families-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  opaque
    min-inhabited-finitely-enumerable-subset-ℝ : ℝ l2
    min-inhabited-finitely-enumerable-subset-ℝ =
      neg-ℝ
        ( max-inhabited-finitely-enumerable-subset-ℝ
          ( neg-finitely-enumerable-subset-ℝ S)
          ( neg-is-inhabited-subset-ℝ
            ( subset-finitely-enumerable-subset-ℝ S)
            ( |S|)))
```

## Properties

### The minimum is the infimum

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  opaque
    unfolding min-inhabited-finitely-enumerable-subset-ℝ

    is-infimum-min-inhabited-finitely-enumerable-subset-ℝ :
      is-infimum-subset-ℝ
        ( subset-finitely-enumerable-subset-ℝ S)
        ( min-inhabited-finitely-enumerable-subset-ℝ S |S|)
    is-infimum-min-inhabited-finitely-enumerable-subset-ℝ =
      is-infimum-neg-supremum-neg-subset-ℝ
        ( subset-finitely-enumerable-subset-ℝ S)
        ( max-inhabited-finitely-enumerable-subset-ℝ _ _)
        ( is-supremum-max-inhabited-finitely-enumerable-subset-ℝ _ _)
```

### Finitely enumerable subsets of the real numbers have an infimum

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  has-infimum-inhabited-finitely-enumerable-subset-ℝ :
    has-infimum-subset-ℝ (subset-finitely-enumerable-subset-ℝ S) l2
  has-infimum-inhabited-finitely-enumerable-subset-ℝ =
    ( min-inhabited-finitely-enumerable-subset-ℝ S |S| ,
      is-infimum-min-inhabited-finitely-enumerable-subset-ℝ S |S|)
```

### The minimum is the greatest lower bound

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  abstract
    is-greatest-lower-bound-min-inhabited-finitely-enumerable-subset-ℝ :
      is-greatest-lower-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( min-inhabited-finitely-enumerable-subset-ℝ S |S|)
    is-greatest-lower-bound-min-inhabited-finitely-enumerable-subset-ℝ =
      is-greatest-lower-bound-is-infimum-family-ℝ
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( min-inhabited-finitely-enumerable-subset-ℝ S |S|)
        ( is-infimum-min-inhabited-finitely-enumerable-subset-ℝ S |S|)
```

### The minimum is a lower bound

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  abstract
    is-lower-bound-min-inhabited-finitely-enumerable-subset-ℝ :
      is-lower-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( min-inhabited-finitely-enumerable-subset-ℝ S |S|)
    is-lower-bound-min-inhabited-finitely-enumerable-subset-ℝ =
      is-lower-bound-is-infimum-family-ℝ
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( min-inhabited-finitely-enumerable-subset-ℝ S |S|)
        ( is-infimum-min-inhabited-finitely-enumerable-subset-ℝ S |S|)
```

### The minimum is approximated above

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  abstract
    is-approximated-above-min-inhabited-finitely-enumerable-subset-ℝ :
      is-approximated-above-family-ℝ
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( min-inhabited-finitely-enumerable-subset-ℝ S |S|)
    is-approximated-above-min-inhabited-finitely-enumerable-subset-ℝ =
      is-approximated-above-is-infimum-family-ℝ
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( min-inhabited-finitely-enumerable-subset-ℝ S |S|)
        ( is-infimum-min-inhabited-finitely-enumerable-subset-ℝ S |S|)
```
