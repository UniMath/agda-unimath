# Subsets of groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.subsets-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-locale-of-subtypes funext
open import foundation.sets funext
open import foundation.universe-levels

open import group-theory.groups funext

open import order-theory.large-locales funext
open import order-theory.large-posets funext
```

</details>

## Idea

A **subset** of a [group](group-theory.groups.md) `G` is a
[subtype](foundation.subtypes.md) of the underlying type of `G`. The
[large poset](order-theory.large-posets.md) of all subsets of `G` is called the
**powerset** of `G`.

## Definitions

### The large locale of subsets of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  powerset-large-locale-Group :
    Large-Locale (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3) lzero
  powerset-large-locale-Group = powerset-Large-Locale (type-Group G)
```

### The large poset of subsets of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  powerset-large-poset-Group :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  powerset-large-poset-Group =
    large-poset-Large-Locale (powerset-large-locale-Group G)
```

### Subsets of groups

```agda
subset-Group :
  (l : Level) {l1 : Level} (G : Group l1) → UU (lsuc l ⊔ l1)
subset-Group l G = type-Large-Locale (powerset-large-locale-Group G) l

is-set-subset-Group :
  {l1 l2 : Level} (G : Group l1) → is-set (subset-Group l2 G)
is-set-subset-Group G =
  is-set-type-Large-Locale (powerset-large-locale-Group G)
```
