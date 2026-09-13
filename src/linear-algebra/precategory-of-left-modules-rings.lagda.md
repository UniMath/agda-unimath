# The precategory of left modules over a ring

```agda
module linear-algebra.precategory-of-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

[Left modules](linear-algebra.left-modules-rings.md) over a
[ring](ring-theory.rings.md) and
[linear maps](linear-algebra.linear-maps-left-modules-rings.md) between them
form a [large precategory](category-theory.large-precategories.md).

## Definition

```agda
module _
  {l1 : Level}
  (R : Ring l1)
  where

  large-precategory-left-module-Ring :
    Large-Precategory (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-precategory-left-module-Ring =
    make-Large-Precategory
      ( λ l2 → left-module-Ring l2 R)
      ( hom-set-left-module-Ring R)
      ( λ {X = X} {Y = Y} {Z = Z} → comp-linear-map-left-module-Ring R X Y Z)
      ( λ {X = X} → id-linear-map-left-module-Ring R X)
      ( λ {X = X} {Y = Y} {Z = Z} {W = W} →
        associative-comp-linear-map-left-module-Ring R X Y Z W)
      ( λ {X = X} {Y = Y} →
        left-unit-law-comp-linear-map-left-module-Ring R X Y)
      ( λ {X = X} {Y = Y} →
        right-unit-law-comp-linear-map-left-module-Ring R X Y)
```
