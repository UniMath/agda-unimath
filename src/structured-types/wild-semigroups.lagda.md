# Wild semigroups

```agda
module structured-types.wild-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.magmas
```

</details>

## Idea

A {{#concept "wild semigroup" Agda=Wild-Semigroup}} is a
[magma](structured-types.magmas.md) with an associative multiplication.

## Definition

```agda
Wild-Semigroup : (l : Level) → UU (lsuc l)
Wild-Semigroup l =
  Σ ( Magma l)
    ( λ M →
      (x y z : type-Magma M) →
      mul-Magma M (mul-Magma M x y) z ＝ mul-Magma M x (mul-Magma M y z))

module _
  {l : Level} (G : Wild-Semigroup l)
  where

  magma-Wild-Semigroup : Magma l
  magma-Wild-Semigroup = pr1 G

  type-Wild-Semigroup : UU l
  type-Wild-Semigroup = type-Magma magma-Wild-Semigroup

  mul-Wild-Semigroup : (x y : type-Wild-Semigroup) → type-Wild-Semigroup
  mul-Wild-Semigroup = mul-Magma magma-Wild-Semigroup

  mul-Wild-Semigroup' : (x y : type-Wild-Semigroup) → type-Wild-Semigroup
  mul-Wild-Semigroup' = mul-Magma' magma-Wild-Semigroup

  associative-mul-Wild-Semigroup :
    (x y z : type-Wild-Semigroup) →
    mul-Wild-Semigroup (mul-Wild-Semigroup x y) z ＝
    mul-Wild-Semigroup x (mul-Wild-Semigroup y z)
  associative-mul-Wild-Semigroup = pr2 G
```
