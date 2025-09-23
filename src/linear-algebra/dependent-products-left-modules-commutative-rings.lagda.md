# Dependent products of left modules over commutative rings

```agda
module linear-algebra.dependent-products-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.function-extensionality
open import foundation.universe-levels

open import linear-algebra.dependent-products-left-modules-rings
open import linear-algebra.left-modules-commutative-rings
```

</details>

## Idea

Given a [commutative ring](commutative-algebra.commutative-rings.md) `R` and a
family of [left modules](linear-algebra.left-modules-commutative-rings.md) `Mᵢ`
over `R` indexed by `i : I`, the dependent product `Π (i : I) Mᵢ` is a left
module over `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Ring l1) (I : UU l2)
  (M : I → left-module-Commutative-Ring l3 R)
  where

  Π-left-module-Commutative-Ring : left-module-Commutative-Ring (l2 ⊔ l3) R
  Π-left-module-Commutative-Ring =
    Π-left-module-Ring (ring-Commutative-Ring R) I M
```
