# The precategory of left modules over commutative rings

```agda
module linear-algebra.precategory-of-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import commutative-algebra.commutative-rings

open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.precategory-of-left-modules-rings
```

</details>

## Idea

[Left modules](linear-algebra.left-modules-commutative-rings.md) over a given
[commutative ring](commutative-algebra.commutative-rings.md) and
[linear maps](linear-algebra.linear-maps-left-modules-commutative-rings.md)
between them form a [large precategory](category-theory.large-precategories.md).

## Definition

```agda
module _
  {l1 : Level}
  (R : Commutative-Ring l1)
  where

  large-precategory-left-module-Commutative-Ring :
    Large-Precategory (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-precategory-left-module-Commutative-Ring =
    large-precategory-left-module-Ring (ring-Commutative-Ring R)
```
