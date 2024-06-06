# Commuting squares of morphisms in large precategories

```agda
module category-theory.commuting-squares-of-morphisms-in-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A square of morphisms

```text
  x ──────> y
  │         │
  │         │
  ∨         ∨
  z ──────> w
```

in a [large precategory](category-theory.large-precategories.md) `C` is said to
**commute** if there is an [identification](foundation-core.identity-types.md)
between both composites.

## Definitions

```agda
coherence-square-hom-Large-Precategory :
  {l1 l2 l3 l4 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (C : Large-Precategory α β)
  {x : obj-Large-Precategory C l1}
  {y : obj-Large-Precategory C l2}
  {z : obj-Large-Precategory C l3}
  {w : obj-Large-Precategory C l4}
  (top : hom-Large-Precategory C x y)
  (left : hom-Large-Precategory C x z)
  (right : hom-Large-Precategory C y w)
  (bottom : hom-Large-Precategory C z w) →
  UU (β l1 l4)
coherence-square-hom-Large-Precategory C top left right bottom =
  ( comp-hom-Large-Precategory C bottom left) ＝
  ( comp-hom-Large-Precategory C right top)
```
