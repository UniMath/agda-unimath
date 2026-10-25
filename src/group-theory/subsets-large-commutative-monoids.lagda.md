# Subsets of large commutative monoids

```agda
module group-theory.subsets-large-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.large-commutative-monoids
open import group-theory.subsets-large-monoids
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a large commutative monoid" Agda=subset-Large-Commutative-Monoid}}
of a [large commutative monoid](group-theory.large-commutative-monoids.md) is a
[subset](foundation.subsets-cumulative-large-sets.md) of the
[cumulative large set](foundation.cumulative-large-sets.md) of the large
commutative monoid.

## Definition

```agda
subset-Large-Commutative-Monoid :
  {α : Level → Level} {β : Level → Level → Level} →
  (Level → Level) → Large-Commutative-Monoid α β → UUω
subset-Large-Commutative-Monoid γ M =
  subset-Large-Monoid γ (large-monoid-Large-Commutative-Monoid M)
```

## Properties

### The property of being closed under multiplication

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  (S : subset-Large-Commutative-Monoid γ M)
  where

  is-closed-under-mul-subset-Large-Commutative-Monoid : UUω
  is-closed-under-mul-subset-Large-Commutative-Monoid =
    is-closed-under-mul-subset-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)
      ( S)
```

### The property of containing the unit

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  (S : subset-Large-Commutative-Monoid γ M)
  where

  contains-unit-prop-subset-Large-Commutative-Monoid : Prop (γ lzero)
  contains-unit-prop-subset-Large-Commutative-Monoid =
    contains-unit-prop-subset-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)
      ( S)

  contains-unit-subset-Large-Commutative-Monoid : UU (γ lzero)
  contains-unit-subset-Large-Commutative-Monoid =
    type-Prop contains-unit-prop-subset-Large-Commutative-Monoid
```
