# Subsets of large monoids

```agda
module group-theory.subsets-large-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.subsets-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.large-monoids
open import group-theory.subsets-large-semigroups
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a large monoid" Agda=subset-Large-Monoid}}
of a [large monoid](group-theory.large-monoids.md) is a
[subset](foundation.subsets-cumulative-large-sets.md) of the
[cumulative large set](foundation.cumulative-large-sets.md) of the large monoid.

## Definition

```agda
subset-Large-Monoid :
  {α : Level → Level} {β : Level → Level → Level} →
  (Level → Level) → Large-Monoid α β → UUω
subset-Large-Monoid γ M =
  subset-Large-Semigroup γ (large-semigroup-Large-Monoid M)

module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (M : Large-Monoid α β)
  (S : subset-Large-Monoid γ M)
  where

  type-subset-Large-Monoid :
    (l : Level) → UU (α l ⊔ γ l)
  type-subset-Large-Monoid =
    type-subset-Large-Semigroup (large-semigroup-Large-Monoid M) S

  is-in-subset-Large-Monoid :
    {l : Level} → type-Large-Monoid M l → UU (γ l)
  is-in-subset-Large-Monoid =
    is-in-subset-Large-Semigroup (large-semigroup-Large-Monoid M) S

  prop-is-in-subset-Large-Monoid :
    {l : Level} → type-Large-Monoid M l → Prop (γ l)
  prop-is-in-subset-Large-Monoid =
    prop-is-in-subset-Large-Semigroup (large-semigroup-Large-Monoid M) S

  abstract
    is-closed-under-raise-subset-Large-Monoid :
      {l1 : Level} (l2 : Level) (x : type-Large-Monoid M l1) →
      is-in-subset-Large-Monoid x →
      is-in-subset-Large-Monoid (raise-Large-Monoid M l2 x)
    is-closed-under-raise-subset-Large-Monoid =
      is-closed-under-raise-subset-Large-Semigroup
        ( large-semigroup-Large-Monoid M)
        ( S)
```

## Properties

### The property of being closed under multiplication

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  (S : subset-Large-Monoid γ M)
  where

  is-closed-under-mul-subset-Large-Monoid : UUω
  is-closed-under-mul-subset-Large-Monoid =
    is-closed-under-mul-subset-Large-Semigroup
      ( large-semigroup-Large-Monoid M)
      ( S)
```

### The property of containing the unit

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  (S : subset-Large-Monoid γ M)
  where

  contains-unit-prop-subset-Large-Monoid : Prop (γ lzero)
  contains-unit-prop-subset-Large-Monoid =
    prop-is-in-subset-Large-Monoid M S (unit-Large-Monoid M)

  contains-unit-subset-Large-Monoid : UU (γ lzero)
  contains-unit-subset-Large-Monoid =
    type-Prop contains-unit-prop-subset-Large-Monoid
```
