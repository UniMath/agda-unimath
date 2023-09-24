# Commuting squares of morphisms in precategories

```agda
module category-theory.commuting-squares-of-morphisms-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A square of morphisms

```text
  x ------> y
  |         |
  |         |
  V         V
  z ------> w
```

is said to **commute** in a [precategory](category-theory.precategories.md) `C`
if there is an [identification](foundation-core.identity-types.md) between both
composites.

## Definitions

```agda
coherence-square-hom-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) {x y z w : obj-Precategory C}
  (top : hom-Precategory C x y)
  (left : hom-Precategory C x z)
  (right : hom-Precategory C y w)
  (bottom : hom-Precategory C z w) →
  UU l2
coherence-square-hom-Precategory C top left right bottom =
  (comp-hom-Precategory C bottom left) ＝ (comp-hom-Precategory C right top)
```
