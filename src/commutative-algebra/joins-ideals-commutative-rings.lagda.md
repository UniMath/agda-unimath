# Joins of ideals in commutative rings

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module commutative-algebra.joins-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.poset-of-ideals-commutative-rings
open import commutative-algebra.products-of-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.universe-levels

open import order-theory.least-upper-bounds-large-posets

open import ring-theory.joins-ideals-rings
```

</details>

## Idea

The **join** of a family of
[ideals](commutative-algebra.ideals-commutative-rings.md) `i ↦ J i` in a
[commutative ring](commutative-algebra.commutative-rings.md) is the least ideal
containing each `J i`.

## Definition

### The universal property of the join of a family of ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  {I : UU l2} (J : I → ideal-Commutative-Ring l3 A)
  where

  is-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 A) → UUω
  is-join-family-of-ideals-Commutative-Ring =
    is-join-family-of-ideals-Ring (ring-Commutative-Ring A) J
```

### The join of a family of ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  {I : UU l2} (J : I → ideal-Commutative-Ring l3 A)
  where

  generating-subset-join-family-of-ideals-Commutative-Ring :
    subset-Commutative-Ring (l2 ⊔ l3) A
  generating-subset-join-family-of-ideals-Commutative-Ring =
    generating-subset-join-family-of-ideals-Ring (ring-Commutative-Ring A) J

  join-family-of-ideals-Commutative-Ring :
    ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  join-family-of-ideals-Commutative-Ring =
    join-family-of-ideals-Ring (ring-Commutative-Ring A) J

  forward-implication-is-join-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 A) →
    ((i : I) → leq-ideal-Commutative-Ring A (J i) K) →
    leq-ideal-Commutative-Ring A join-family-of-ideals-Commutative-Ring K
  forward-implication-is-join-join-family-of-ideals-Commutative-Ring =
    forward-implication-is-join-join-family-of-ideals-Ring
      ( ring-Commutative-Ring A)
      ( J)

  backward-implication-is-join-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 A) →
    leq-ideal-Commutative-Ring A join-family-of-ideals-Commutative-Ring K →
    (i : I) → leq-ideal-Commutative-Ring A (J i) K
  backward-implication-is-join-join-family-of-ideals-Commutative-Ring =
    backward-implication-is-join-join-family-of-ideals-Ring
      ( ring-Commutative-Ring A)
      ( J)

  is-join-join-family-of-ideals-Commutative-Ring :
    is-join-family-of-ideals-Commutative-Ring A J
      join-family-of-ideals-Commutative-Ring
  is-join-join-family-of-ideals-Commutative-Ring =
    is-join-join-family-of-ideals-Ring (ring-Commutative-Ring A) J
```

## Properties

### Products distribute over joins of families of ideals

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A)
  {U : UU l3} (J : U → ideal-Commutative-Ring l4 A)
  where

  forward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-ideals-Commutative-Ring A J))
      ( join-family-of-ideals-Commutative-Ring A
        ( λ α →
          product-ideal-Commutative-Ring A I (J α)))
  forward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ring =
    {!!}
```
