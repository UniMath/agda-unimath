# Commuting squares of morphisms in precategories

```agda
module category-theory.commuting-squares-of-morphisms-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-set-magmoids
open import category-theory.precategories

open import foundation.action-on-identifications-functions
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

pasting-horizontal-coherence-square-hom-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y z w a b : obj-Precategory C}
  (topleft : hom-Precategory C x y)
  (topright : hom-Precategory C y a)
  (left : hom-Precategory C x z)
  (middle : hom-Precategory C y w)
  (right : hom-Precategory C a b)
  (bottomleft : hom-Precategory C z w)
  (bottomright : hom-Precategory C w b) →
  coherence-square-hom-Precategory C topleft left middle bottomleft →
  coherence-square-hom-Precategory C topright middle right bottomright →
  coherence-square-hom-Precategory C
    ( comp-hom-Precategory C topright topleft)
    ( left)
    ( right)
    ( comp-hom-Precategory C bottomright bottomleft)
pasting-horizontal-coherence-square-hom-Precategory C
  topleft topright left middle right bottomleft bottomright commleft commright =
  ( associative-comp-hom-Precategory C _ _ _) ∙
  ( ap (postcomp-hom-Precategory C bottomright _) commleft) ∙
  ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
  ( ap (precomp-hom-Precategory C topleft _) commright) ∙
  ( associative-comp-hom-Precategory C _ _ _)
```
