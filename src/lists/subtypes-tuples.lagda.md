# Subtypes of tuples

```agda
module lists.subtypes-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
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

  map-inclusion-subtype-tuple :
    {n : ℕ} → tuple (type-subtype S) n → tuple A n
  map-inclusion-subtype-tuple = map-tuple (inclusion-subtype S)

  all-tuple-map-inclusion-subtype-tuple :
    {n : ℕ} (xs : tuple (type-subtype S) n) →
    all-tuple (is-in-subtype S) (map-inclusion-subtype-tuple xs)
  all-tuple-map-inclusion-subtype-tuple empty-tuple = raise-star
  all-tuple-map-inclusion-subtype-tuple ((x , x∈S) ∷ xs) =
    ( x∈S , all-tuple-map-inclusion-subtype-tuple xs)
```

## Properties

### Choice on tuple subtypes formed by propositional truncation

```agda
module _
  {l1 l2 : Level}
  {X : UU l1}
  {F : X → UU l2}
  where

  abstract
    choice-all-trunc-prop-tuple :
      {n : ℕ} (xs : tuple X n) → all-tuple (type-trunc-Prop ∘ F) xs →
      type-trunc-Prop (all-tuple F xs)
    choice-all-trunc-prop-tuple empty-tuple _ = unit-trunc-Prop raise-star
    choice-all-trunc-prop-tuple (x ∷ xs) (|Fx| , |Fxs|) =
      map-binary-trunc-Prop (_,_) |Fx| (choice-all-trunc-prop-tuple xs |Fxs|)
```

### If `S ⊆ T`, then `all-tuple-subtype S ⊆ all-tuple-subtype T`

```agda
module _
  {l1 l2 l3 : Level}
  {X : UU l1}
  (S : subtype l2 X)
  (T : subtype l3 X)
  where

  leq-all-tuple-subtype :
    S ⊆ T → (n : ℕ) → all-tuple-subtype S n ⊆ all-tuple-subtype T n
  leq-all-tuple-subtype S⊆T 0 empty-tuple _ = raise-star
  leq-all-tuple-subtype S⊆T (succ-ℕ n) (x ∷ xs) (x∈S , xs⊆S) =
    ( S⊆T x x∈S , leq-all-tuple-subtype S⊆T n xs xs⊆S)
```
