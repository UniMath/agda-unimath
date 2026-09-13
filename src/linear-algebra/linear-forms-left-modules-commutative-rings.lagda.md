# Linear forms in left modules over commutative rings

```agda
module linear-algebra.linear-forms-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
```

</details>

## Idea

A
{{#concept "linear form" Disambiguation="in a left module over a commutative ring" Agda=linear-form-left-module-Commutative-Ring}}
in a [left module](linear-algebra.left-modules-commutative-rings.md) `M` over a
[commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[linear map](linear-algebra.linear-maps-left-modules-commutative-rings.md) from
`M` to `R`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  linear-form-left-module-Commutative-Ring : UU (l1 ⊔ l2)
  linear-form-left-module-Commutative-Ring =
    linear-map-left-module-Commutative-Ring R
      ( M)
      ( left-module-commutative-ring-Commutative-Ring R)

  map-linear-form-left-module-Commutative-Ring :
    linear-form-left-module-Commutative-Ring →
    type-left-module-Commutative-Ring R M →
    type-Commutative-Ring R
  map-linear-form-left-module-Commutative-Ring =
    map-linear-map-left-module-Commutative-Ring R
      ( M)
      ( left-module-commutative-ring-Commutative-Ring R)
```

## See also

- [Duals of left modules over commutative rings](linear-algebra.duals-left-modules-commutative-rings.md),
  the left module of linear forms
