# Cyclic types

```agda
module structured-types.cyclic-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers

open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels
```

</details>

## Idea

A **cyclic set** consists of an [inhabited](foundation.inhabited-types.md)
[set](foundation.sets.md) `A` equipped with an
[automorphism](foundation.automorphisms.md) `e : A ≃ A` which is _cyclic_ in the
sense that the map

```text
  k ↦ eᵏ x
```

is [surjective](foundation.surjective-maps.md) for every `x : A`. There are
several equivalent ways of stating the concept of cyclic sets. Two further
equivalent ways are:

- A cyclic set is a
  [connected set bundle](synthetic-homotopy-theory.connected-set-bundles-circle.md)
  over the [circle](synthetic-homotopy-theory.circle.md).
- A cyclic set is a set which is a [`C`-torsor](group-theory.torsors.md) for
  some [cyclic group](group-theory.cyclic-groups.md) `C`.

## Definition

### The predicate of being a cyclic set

```agda
module _
  {l : Level} (X : Set l) (e : type-Set X ≃ type-Set X)
  where

  is-cyclic-prop-Set : Prop l
  is-cyclic-prop-Set =
    prod-Prop
      ( trunc-Prop (type-Set X))
      ( Π-Prop
        ( type-Set X)
        ( λ x →
          is-surjective-Prop (λ k → map-iterate-automorphism-ℤ k e x)))

  is-cyclic-Set : UU l
  is-cyclic-Set = type-Prop is-cyclic-prop-Set

Cyclic-Set : (l : Level) → UU (lsuc l)
Cyclic-Set l =
  Σ (Set l) (λ X → Σ (type-Set X ≃ type-Set X) (λ e → is-cyclic-Set X e))
```
