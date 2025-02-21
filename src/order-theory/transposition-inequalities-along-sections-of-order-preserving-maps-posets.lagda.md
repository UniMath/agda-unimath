# Transposing inequalities in posets along sections of order-preserving maps

```agda
module order-theory.transposition-inequalities-along-sections-of-order-preserving-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.sections
open import foundation.identity-types

open import order-theory.posets
open import order-theory.order-preserving-maps-posets
```

## Idea

Given a pair of posets `P` and `Q`, consider an
[order preserving map](order-theory.order-preserving-maps-posets.md)
`f : type-Poset P → type-Poset Q` and a map
`g : type-Poset Q → type-Poset P` in the converse direction.
Then there is a family of transposition maps

```text
x ≤ g y → f x ≤ y
```

indexed by `x : type-Poset P` and `y : type-Poset Q`.
