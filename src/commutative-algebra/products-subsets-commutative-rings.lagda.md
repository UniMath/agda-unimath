# Products of subsets of commutative rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra.products-subsets-commutative-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings funext univalence truncations
open import commutative-algebra.subsets-commutative-rings funext univalence truncations

open import foundation.identity-types funext
open import foundation.subtypes funext univalence truncations
open import foundation.unions-subtypes funext univalence truncations
open import foundation.universe-levels

open import ring-theory.products-subsets-rings funext univalence truncations
```

</details>

## Idea

The **product** of two
[subsets](commutative-algebra.subsets-commutative-rings.md) `S` and `T` of a
[commutative ring](commutative-algebra.commutative-rings.md) `A` is the subset
consistng of products `xy` where `x ∈ S` and `y ∈ T`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (S : subset-Commutative-Ring l2 A) (T : subset-Commutative-Ring l3 A)
  where

  product-subset-Commutative-Ring : subset-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  product-subset-Commutative-Ring =
    product-subset-Ring (ring-Commutative-Ring A) S T
```

## Properties

### The product of subsets of commutative rings is associative

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (R : subset-Commutative-Ring l2 A)
  (S : subset-Commutative-Ring l3 A)
  (T : subset-Commutative-Ring l4 A)
  where

  forward-inclusion-associative-product-subset-Commutative-Ring :
    ( product-subset-Commutative-Ring A
      ( product-subset-Commutative-Ring A R S)
      ( T)) ⊆
    ( product-subset-Commutative-Ring A
      ( R)
      ( product-subset-Commutative-Ring A S T))
  forward-inclusion-associative-product-subset-Commutative-Ring =
    forward-inclusion-associative-product-subset-Ring
      ( ring-Commutative-Ring A)
      ( R)
      ( S)
      ( T)

  backward-inclusion-associative-product-subset-Commutative-Ring :
    ( product-subset-Commutative-Ring A
      ( R)
      ( product-subset-Commutative-Ring A S T)) ⊆
    ( product-subset-Commutative-Ring A
      ( product-subset-Commutative-Ring A R S)
      ( T))
  backward-inclusion-associative-product-subset-Commutative-Ring =
    backward-inclusion-associative-product-subset-Ring
      ( ring-Commutative-Ring A)
      ( R)
      ( S)
      ( T)

  associative-product-subset-Commutative-Ring :
    product-subset-Commutative-Ring A
      ( product-subset-Commutative-Ring A R S)
      ( T) ＝
    product-subset-Commutative-Ring A
      ( R)
      ( product-subset-Commutative-Ring A S T)
  associative-product-subset-Commutative-Ring =
    associative-product-subset-Ring (ring-Commutative-Ring A) R S T
```

### Products distribute over unions of families of subsets

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (S : subset-Commutative-Ring l2 A)
  {I : UU l3} (T : I → subset-Commutative-Ring l4 A)
  where

  forward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ring :
    product-subset-Commutative-Ring A S (union-family-of-subtypes T) ⊆
    union-family-of-subtypes (λ i → product-subset-Commutative-Ring A S (T i))
  forward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ring =
    forward-inclusion-distributive-product-union-family-of-subsets-Ring
      ( ring-Commutative-Ring A)
      ( S)
      ( T)

  backward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ring :
    union-family-of-subtypes
      ( λ i → product-subset-Commutative-Ring A S (T i)) ⊆
    product-subset-Commutative-Ring A S (union-family-of-subtypes T)
  backward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ring =
    backward-inclusion-distributive-product-union-family-of-subsets-Ring
      ( ring-Commutative-Ring A)
      ( S)
      ( T)

  distributive-product-union-family-of-subsets-Commutative-Ring :
    product-subset-Commutative-Ring A S (union-family-of-subtypes T) ＝
    union-family-of-subtypes (λ i → product-subset-Commutative-Ring A S (T i))
  distributive-product-union-family-of-subsets-Commutative-Ring =
    distributive-product-union-family-of-subsets-Ring
      ( ring-Commutative-Ring A)
      ( S)
      ( T)
```
