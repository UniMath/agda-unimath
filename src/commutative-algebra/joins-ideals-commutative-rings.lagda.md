# Joins of ideals in commutative rings

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module commutative-algebra.joins-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.ideals-generated-by-subsets-commutative-rings
open import commutative-algebra.poset-of-ideals-commutative-rings
open import commutative-algebra.products-of-ideals-commutative-rings
open import commutative-algebra.products-subsets-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.unions-subtypes
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
    generating-subset-join-family-of-ideals-Ring
      ( ring-Commutative-Ring A)
      ( J)

  join-family-of-ideals-Commutative-Ring :
    ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  join-family-of-ideals-Commutative-Ring =
    join-family-of-ideals-Ring (ring-Commutative-Ring A) J

  forward-inclusion-is-join-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 A) →
    ((i : I) → leq-ideal-Commutative-Ring A (J i) K) →
    leq-ideal-Commutative-Ring A join-family-of-ideals-Commutative-Ring K
  forward-inclusion-is-join-join-family-of-ideals-Commutative-Ring =
    forward-inclusion-is-join-join-family-of-ideals-Ring
      ( ring-Commutative-Ring A)
      ( J)

  backward-inclusion-is-join-join-family-of-ideals-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 A) →
    leq-ideal-Commutative-Ring A join-family-of-ideals-Commutative-Ring K →
    (i : I) → leq-ideal-Commutative-Ring A (J i) K
  backward-inclusion-is-join-join-family-of-ideals-Commutative-Ring =
    backward-inclusion-is-join-join-family-of-ideals-Ring
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
  forward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ring
    x p =
    preserves-order-ideal-subset-Commutative-Ring A
      ( product-subset-Commutative-Ring A
        ( subset-ideal-Commutative-Ring A I)
        ( union-family-of-subtypes
          ( λ α → subset-ideal-Commutative-Ring A (J α))))
      ( generating-subset-join-family-of-ideals-Commutative-Ring A
        ( λ α → product-ideal-Commutative-Ring A I (J α)))
      ( transitive-leq-subtype
        ( product-subset-Commutative-Ring A
          ( subset-ideal-Commutative-Ring A I)
          ( union-family-of-subtypes
            ( λ α → subset-ideal-Commutative-Ring A (J α))))
        ( union-family-of-subtypes
          ( λ α →
            generating-subset-product-ideal-Commutative-Ring A I (J α)))
        ( generating-subset-join-family-of-ideals-Commutative-Ring A
          ( λ α → product-ideal-Commutative-Ring A I (J α)))
        ( preserves-order-union-family-of-subtypes
          ( λ α → generating-subset-product-ideal-Commutative-Ring A I (J α))
          ( λ α → subset-product-ideal-Commutative-Ring A I (J α))
          ( λ α →
            contains-subset-ideal-subset-Commutative-Ring A
              ( generating-subset-product-ideal-Commutative-Ring A I (J α))))
        ( forward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ring
          ( A)
          ( subset-ideal-Commutative-Ring A I)
          ( λ α → subset-ideal-Commutative-Ring A (J α))))
      ( x)
      ( backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring
         ( A)
         ( I)
         ( generating-subset-join-family-of-ideals-Commutative-Ring A J)
         ( x)
         ( p))

  backward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( join-family-of-ideals-Commutative-Ring A
        ( λ α →
          product-ideal-Commutative-Ring A I (J α)))
      ( product-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-ideals-Commutative-Ring A J))
  backward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ring
    x p =
    forward-inclusion-right-preserves-product-ideal-subset-Commutative-Ring A I
      ( generating-subset-join-family-of-ideals-Commutative-Ring A J)
      ( x)
      ( transitive-leq-subtype
        ( generating-subset-join-family-of-ideals-Commutative-Ring A
          ( λ α → product-ideal-Commutative-Ring A I (J α)))
        ( union-family-of-subtypes
          ( λ α →
            generating-subset-product-ideal-Commutative-Ring A I (J α)))
        {!!}
        {!!}
        {!!}
        {!!}
        {!!})
```
