# Commuting squares of morphisms in precategories

```agda
module category-theory.commuting-squares-of-morphisms-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-set-magmoids
open import category-theory.precategories

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

in a [precategory](category-theory.precategories.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between both
composites:

```text
  bottom ∘ left ＝ right ∘ top.
```

## Definitions

```agda
coherence-square-hom-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) {x y z w : obj-Precategory C}
  (top : hom-Precategory C x y)
  (left : hom-Precategory C x z)
  (right : hom-Precategory C y w)
  (bottom : hom-Precategory C z w) →
  UU l2
coherence-square-hom-Precategory C =
  coherence-square-hom-Set-Magmoid (set-magmoid-Precategory C)
```
