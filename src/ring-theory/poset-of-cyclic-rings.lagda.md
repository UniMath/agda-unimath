# The poset of cyclic rings

```agda
module ring-theory.poset-of-cyclic-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.large-posets

open import ring-theory.category-of-cyclic-rings
```

</details>

## Idea

The
{{#concept "large poset" Disambiguation="of cyclic rings" Agda=Cyclic-Ring-Large-Poset}}
of [cyclic rings](ring-theory.cyclic-rings.md) is the
[large category of cyclic rings](ring-theory.category-of-cyclic-rings.md), which
happens to be a [large poset](order-theory.large-posets.md).

The large poset of cyclic rings is dual to the large poset of
[subgroups](group-theory.subgroups.md) of the
[group of integers](elementary-number-theory.group-of-integers.md).

## Definition

### The large poset of cyclic rings

```agda
Cyclic-Ring-Large-Poset : Large-Poset lsuc (_⊔_)
Cyclic-Ring-Large-Poset =
  large-poset-Large-Category
    ( Cyclic-Ring-Large-Category)
    ( is-large-poset-Cyclic-Ring-Large-Category)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
