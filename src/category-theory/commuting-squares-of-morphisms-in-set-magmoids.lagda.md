# Commuting squares of morphisms in set-magmoids

```agda
module category-theory.commuting-squares-of-morphisms-in-set-magmoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.set-magmoids

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
  ∨         ∨
  z ------> w
```

in a [set-magmoid](category-theory.set-magmoids.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between both
composites:

```text
  bottom ∘ left ＝ right ∘ top.
```

## Definitions

```agda
coherence-square-hom-Set-Magmoid :
  {l1 l2 : Level} (C : Set-Magmoid l1 l2)
  {x y z w : obj-Set-Magmoid C}
  (top : hom-Set-Magmoid C x y)
  (left : hom-Set-Magmoid C x z)
  (right : hom-Set-Magmoid C y w)
  (bottom : hom-Set-Magmoid C z w) →
  UU l2
coherence-square-hom-Set-Magmoid C top left right bottom =
  ( comp-hom-Set-Magmoid C bottom left) ＝
  ( comp-hom-Set-Magmoid C right top)
```
