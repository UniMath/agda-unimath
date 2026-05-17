# Subtypes of tuples

```agda
module lists.subtypes-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import lists.functoriality-tuples
open import lists.tuples
```

</details>

## Idea

A [subtype](foundation.subtypes.md) of a type `A` induces a subtype of
`n`-[tuples](lists.tuples.md) in `A`.

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (S : subtype l2 A)
  where

  abstract
    is-subtype-all-tuple :
      {n : ℕ} →
      is-subtype (all-tuple {n = n} (is-in-subtype S))
    is-subtype-all-tuple {0} empty-tuple = is-prop-raise-unit
    is-subtype-all-tuple {succ-ℕ n} (x ∷ xs) =
      is-prop-product (is-prop-is-in-subtype S x) (is-subtype-all-tuple xs)

  all-tuple-subtype : (n : ℕ) → subtype l2 (tuple A n)
  all-tuple-subtype n xs =
    ( all-tuple (is-in-subtype S) xs ,
      is-subtype-all-tuple xs)

  all-tuple-tuple-type-subtype :
    {n : ℕ} (xs : tuple (type-subtype S) n) →
    all-tuple (is-in-subtype S) (map-tuple (inclusion-subtype S) xs)
  all-tuple-tuple-type-subtype empty-tuple = map-raise star
  all-tuple-tuple-type-subtype ((x , x∈S) ∷ xs) =
    ( x∈S , all-tuple-tuple-type-subtype xs)
```
