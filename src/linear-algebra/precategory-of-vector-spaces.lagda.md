# The precategory of vector spaces

```agda
module linear-algebra.precategory-of-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import commutative-algebra.heyting-fields

open import foundation.universe-levels

open import linear-algebra.precategory-of-left-modules-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

[Vector spaces](linear-algebra.vector-spaces.md) over a given
[Heyting field](commutative-algebra.heyting-fields.md) and
[linear maps](linear-algebra.linear-maps-vector-spaces.md) form a
[large precategory](category-theory.large-precategories.md).

## Definition

```agda
module _
  {l1 : Level}
  (K : Heyting-Field l1)
  where

  large-precategory-Vector-Space :
    Large-Precategory (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-precategory-Vector-Space =
    large-precategory-left-module-Ring (ring-Heyting-Field K)
```
