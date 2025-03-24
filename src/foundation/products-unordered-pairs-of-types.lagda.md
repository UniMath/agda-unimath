# Products of unordered pairs of types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.products-unordered-pairs-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences funext
open import foundation.functoriality-cartesian-product-types funext
open import foundation.functoriality-dependent-function-types funext univalence
open import foundation.symmetric-operations funext univalence truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.unordered-pairs funext univalence truncations
open import foundation.unordered-pairs-of-types funext univalence truncations

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types

open import univalent-combinatorics.2-element-types funext univalence truncations
open import univalent-combinatorics.universal-property-standard-finite-types funext univalence truncations
```

</details>

## Idea

Given an unordered pair of types, we can take their product. This is a symmetric
version of the cartesian product operation on types.

## Definition

```agda
product-unordered-pair-types :
  {l : Level} → symmetric-operation (UU l) (UU l)
product-unordered-pair-types p =
  (x : type-unordered-pair p) → element-unordered-pair p x

pr-product-unordered-pair-types :
  {l : Level} (p : unordered-pair-types l) (i : type-unordered-pair p) →
  product-unordered-pair-types p → element-unordered-pair p i
pr-product-unordered-pair-types p i f = f i

equiv-pr-product-unordered-pair-types :
  {l : Level} (A : unordered-pair-types l) (i : type-unordered-pair A) →
  product-unordered-pair-types A ≃
  (element-unordered-pair A i × other-element-unordered-pair A i)
equiv-pr-product-unordered-pair-types A i =
  ( ( equiv-product
      ( equiv-tr
        ( element-unordered-pair A)
        ( compute-map-equiv-point-2-Element-Type
          ( 2-element-type-unordered-pair A)
          ( i)))
      ( equiv-tr
        ( element-unordered-pair A)
        ( compute-map-equiv-point-2-Element-Type'
          ( 2-element-type-unordered-pair A)
          ( i)))) ∘e
    ( equiv-dependent-universal-property-Fin-2
      ( ( element-unordered-pair A) ∘
        ( map-equiv-point-2-Element-Type
          ( 2-element-type-unordered-pair A)
          ( i))))) ∘e
  ( equiv-precomp-Π
    ( equiv-point-2-Element-Type (2-element-type-unordered-pair A) (i))
    ( element-unordered-pair A))

equiv-pair-product-unordered-pair-types :
  {l : Level} (A : unordered-pair-types l) (i : type-unordered-pair A) →
  (element-unordered-pair A i × other-element-unordered-pair A i) ≃
  product-unordered-pair-types A
equiv-pair-product-unordered-pair-types A i =
  inv-equiv (equiv-pr-product-unordered-pair-types A i)

pair-product-unordered-pair-types :
  {l : Level} (A : unordered-pair-types l) (i : type-unordered-pair A) →
  element-unordered-pair A i → other-element-unordered-pair A i →
  product-unordered-pair-types A
pair-product-unordered-pair-types A i x y =
  map-equiv (equiv-pair-product-unordered-pair-types A i) (pair x y)
```

### Equivalences of products of unordered pairs of types

```agda
module _
  {l1 l2 : Level} (A : unordered-pair-types l1) (B : unordered-pair-types l2)
  where

  equiv-product-unordered-pair-types :
    equiv-unordered-pair-types A B →
    product-unordered-pair-types A ≃ product-unordered-pair-types B
  equiv-product-unordered-pair-types e =
    equiv-Π
      ( element-unordered-pair B)
      ( equiv-type-equiv-unordered-pair-types A B e)
      ( equiv-element-equiv-unordered-pair-types A B e)
```
