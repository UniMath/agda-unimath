# Subsets of large abelian groups

```agda
module group-theory.subsets-large-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.large-abelian-groups
open import group-theory.subsets-large-groups
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a large abelian group" Agda=subset-Large-Ab}}
of a [large abelian group](group-theory.large-abelian-groups.md) is a
[subset](foundation.subsets-cumulative-large-sets.md) of the
[cumulative large set](foundation.cumulative-large-sets.md) of the large abelian
group.

## Definition

```agda
subset-Large-Ab :
  {α : Level → Level} {β : Level → Level → Level} →
  (Level → Level) → Large-Ab α β → UUω
subset-Large-Ab γ G =
  subset-Large-Group γ (large-group-Large-Ab G)
```

## Properties

### The property of being closed under addition

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  (G : Large-Ab α β)
  (S : subset-Large-Ab γ G)
  where

  is-closed-under-add-subset-Large-Ab : UUω
  is-closed-under-add-subset-Large-Ab =
    is-closed-under-mul-subset-Large-Group
      ( large-group-Large-Ab G)
      ( S)
```

### The property of being closed under negation

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  (G : Large-Ab α β)
  (S : subset-Large-Ab γ G)
  where

  is-closed-under-neg-subset-Large-Ab : UUω
  is-closed-under-neg-subset-Large-Ab =
    is-closed-under-inv-subset-Large-Group
      ( large-group-Large-Ab G)
      ( S)
```

### The property of containing zero

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  (G : Large-Ab α β)
  (S : subset-Large-Ab γ G)
  where

  contains-zero-prop-subset-Large-Ab : Prop (γ lzero)
  contains-zero-prop-subset-Large-Ab =
    contains-unit-prop-subset-Large-Group
      ( large-group-Large-Ab G)
      ( S)

  contains-zero-subset-Large-Ab : UU (γ lzero)
  contains-zero-subset-Large-Ab =
    type-Prop contains-zero-prop-subset-Large-Ab
```
