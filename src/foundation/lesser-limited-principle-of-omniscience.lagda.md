# The lesser limited principle of omniscience

```agda
module foundation.lesser-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.decidable-subtypes
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Statement

The {{#concept "lesser limited principle of omniscience" Agda=LLPO}} (LLPO)
asserts that any pair of [decidable subtypes](foundation.decidable-subtypes.md)
of the [natural numbers](elementary-number-theory.natural-numbers.md) such that
it is not true that both are [inhabited](foundation.inhabited-types.md), either
the first is [empty](foundation.empty-types.md) or the second is empty.

### Instances of LLPO

```agda
instance-LLPO-Prop :
  {l : Level} →
  (S T : decidable-subtype l ℕ) →
  ¬
    ( is-inhabited (type-decidable-subtype S) ×
      is-inhabited (type-decidable-subtype T)) →
  Prop l
instance-LLPO-Prop S T not-both =
  ¬' (is-inhabited-Prop (type-decidable-subtype S)) ∨
  ¬' (is-inhabited-Prop (type-decidable-subtype T))

instance-LLPO :
  {l : Level} →
  (S T : decidable-subtype l ℕ) →
  ¬
    ( is-inhabited (type-decidable-subtype S) ×
      is-inhabited (type-decidable-subtype T)) →
  UU l
instance-LLPO S T not-both = type-Prop (instance-LLPO-Prop S T not-both)
```

### The lesser limited principle of omniscience

```agda
level-LLPO : (l : Level) → UU (lsuc l)
level-LLPO l =
  (S T : decidable-subtype l ℕ) →
  (H :
    ¬
      ( is-inhabited (type-decidable-subtype S) ×
        is-inhabited (type-decidable-subtype T))) →
  instance-LLPO S T H

LLPO : UUω
LLPO = {l : Level} → level-LLPO l
```

## Properties

### The weak limited principle of omniscience implies the lesser limited principle of omniscience

TODO

## Table of choice principles

{{#include tables/choice-principles.md}}

## External links

- [Taboos.LLPO](https://martinescardo.github.io/TypeTopology/Taboos.LLPO.html)
  at TypeTopology
- [lesser limited principle of omniscience](https://ncatlab.org/nlab/show/lesser+limited+principle+of+omniscience)
  at $n$Lab
