# The opposite of a semigroup

```agda
module group-theory.opposite-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

The **opposite of a [semigroup](group-theory.semigroups.md)** `G` with
multiplication `μ` is a semigroup with the same underlying
[set](foundation-core.sets.md) as `G` and multiplication given by `x y ↦ μ y x`.

## Definition

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  set-op-Semigroup : Set l
  set-op-Semigroup = set-Semigroup G

  type-op-Semigroup : UU l
  type-op-Semigroup = type-Set set-op-Semigroup

  mul-op-Semigroup : type-op-Semigroup → type-op-Semigroup → type-op-Semigroup
  mul-op-Semigroup x y = mul-Semigroup G y x

  associative-mul-op-Semigroup :
    (x y z : type-op-Semigroup) →
    mul-Semigroup G z (mul-Semigroup G y x) ＝
    mul-Semigroup G (mul-Semigroup G z y) x
  associative-mul-op-Semigroup x y z = inv (associative-mul-Semigroup G z y x)

  op-Semigroup : Semigroup l
  pr1 op-Semigroup = set-op-Semigroup
  pr1 (pr2 op-Semigroup) = mul-op-Semigroup
  pr2 (pr2 op-Semigroup) = associative-mul-op-Semigroup
```
