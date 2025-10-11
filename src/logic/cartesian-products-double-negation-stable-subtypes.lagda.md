# Cartesian products of double negation stable subtypes

```agda
module logic.cartesian-products-double-negation-stable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.cartesian-products-subtypes
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import logic.double-negation-elimination
open import logic.double-negation-stable-subtypes
```

</details>

## Idea

Given two
[double negation stable subtypes](logic.double-negation-stable-subtypes.md)
`P ⊆ A` and `Q ⊆ B`, then their
[product](foundation.cartesian-products-subtypes.md) is again double negation
stable.

## Definition

### Products of double negation stable subtypes

Given double negation subtypes `P ⊆ A` and `Q ⊆ B`, then `P × Q` is a double
negation stable subtype of `A × Q`.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (P : subtype l3 A) (Q : subtype l4 B)
  where

  is-double-negation-stable-product-subtype :
    is-double-negation-stable-subtype P →
    is-double-negation-stable-subtype Q →
    is-double-negation-stable-subtype (product-subtype P Q)
  is-double-negation-stable-product-subtype p q (a , b) =
    double-negation-elim-product (p a) (q b)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (P : double-negation-stable-subtype l3 A)
  (Q : double-negation-stable-subtype l4 B)
  where

  product-double-negation-stable-subtype :
    double-negation-stable-subtype (l3 ⊔ l4) (A × B)
  product-double-negation-stable-subtype =
    make-double-negation-stable-subtype
      ( product-subtype
        ( subtype-double-negation-stable-subtype P)
        ( subtype-double-negation-stable-subtype Q))
      ( is-double-negation-stable-product-subtype
        ( subtype-double-negation-stable-subtype P)
        ( subtype-double-negation-stable-subtype Q)
        ( is-double-negation-stable-double-negation-stable-subtype P)
        ( is-double-negation-stable-double-negation-stable-subtype Q))
```
