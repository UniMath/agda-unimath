# Commuting triangles of morphisms in precategories

```agda
module category-theory.commuting-triangles-of-morphisms-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-triangles-of-morphisms-in-set-magmoids
open import category-theory.precategories

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

in a [precategory](category-theory.precategories.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between:

```text
  left ＝ right ∘ top.
```

Such a identification is called the
{{#concept "coherence" Disambiguation="commuting triangle of morphisms in precategories" Agda=coherence-triangle-hom-Precategory}}
of the commuting triangle.

## Definitions

```agda
coherence-triangle-hom-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  (top : hom-Precategory C x y)
  (left : hom-Precategory C x z)
  (right : hom-Precategory C y z) →
  UU l2
coherence-triangle-hom-Precategory C =
  coherence-triangle-hom-Set-Magmoid (set-magmoid-Precategory C)
```
