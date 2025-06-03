# Commuting triangles of morphisms in set-magmoids

```agda
module category-theory.commuting-triangles-of-morphisms-in-set-magmoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.set-magmoids

open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A triangle of morphisms

```text
        top
     x ----> y
      \     /
  left \   / right
        ∨ ∨
         z
```

in a [set-magmoid](category-theory.set-magmoids.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between:

```text
  left ＝ right ∘ top.
```

Such a identification is called the
{{#concept "coherence" Disambiguation="commuting triangle of morphisms in set-magmaoids" Agda=coherence-triangle-hom-Set-Magmoid}}
of the commuting triangle.

## Definitions

```agda
coherence-triangle-hom-Set-Magmoid :
  {l1 l2 : Level} (C : Set-Magmoid l1 l2)
  {x y z : obj-Set-Magmoid C}
  (top : hom-Set-Magmoid C x y)
  (left : hom-Set-Magmoid C x z)
  (right : hom-Set-Magmoid C y z) →
  UU l2
coherence-triangle-hom-Set-Magmoid C top left right =
  left ＝ comp-hom-Set-Magmoid C right top
```
