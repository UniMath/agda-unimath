# Subsets of large groups

```agda
module group-theory.subsets-large-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.large-groups
open import group-theory.subsets-large-monoids
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a large group" Agda=subset-Large-Group}}
of a [large group](group-theory.large-groups.md) is a
[subset](foundation.subsets-cumulative-large-sets.md) of the
[cumulative large set](foundation.cumulative-large-sets.md) of the large group.

## Definition

```agda
subset-Large-Group :
  {α : Level → Level} {β : Level → Level → Level} →
  (Level → Level) → Large-Group α β → UUω
subset-Large-Group γ G = subset-Large-Monoid γ (large-monoid-Large-Group G)

module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (G : Large-Group α β)
  (S : subset-Large-Group γ G)
  where

  is-in-subset-Large-Group :
    {l : Level} → type-Large-Group G l → UU (γ l)
  is-in-subset-Large-Group =
    is-in-subset-Large-Monoid (large-monoid-Large-Group G) S
```

## Properties

### The property of being closed under multiplication

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (G : Large-Group α β)
  (S : subset-Large-Group γ G)
  where

  is-closed-under-mul-subset-Large-Group : UUω
  is-closed-under-mul-subset-Large-Group =
    is-closed-under-mul-subset-Large-Monoid
      ( large-monoid-Large-Group G)
      ( S)
```

### The property of containing the unit

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (G : Large-Group α β)
  (S : subset-Large-Group γ G)
  where

  contains-unit-prop-subset-Large-Group : Prop (γ lzero)
  contains-unit-prop-subset-Large-Group =
    contains-unit-prop-subset-Large-Monoid
      ( large-monoid-Large-Group G)
      ( S)

  contains-unit-subset-Large-Group : UU (γ lzero)
  contains-unit-subset-Large-Group =
    type-Prop contains-unit-prop-subset-Large-Group
```

### The property of being closed under inverses

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (G : Large-Group α β)
  (S : subset-Large-Group γ G)
  where

  is-closed-under-inv-subset-Large-Group : UUω
  is-closed-under-inv-subset-Large-Group =
    {l : Level} (x : type-Large-Group G l) →
    is-in-subset-Large-Group G S x →
    is-in-subset-Large-Group G S (inv-Large-Group G x)
```
