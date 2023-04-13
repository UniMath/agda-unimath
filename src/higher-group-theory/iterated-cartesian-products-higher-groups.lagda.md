# Iterated cartesian products of higher groups

```agda
module higher-group-theory.iterated-cartesian-products-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.iterated-cartesian-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import higher-group-theory.cartesian-products-higher-groups
open import higher-group-theory.higher-groups

open import lists.functoriality-lists
open import lists.lists

open import structured-types.iterated-cartesian-products-pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The Cartesian product of higher groups is also an higher group.

## Definition

```agda
iterated-product-∞-Group :
  {l : Level} (L : list (∞-Group l)) → ∞-Group l
iterated-product-∞-Group nil = unit-type-∞-Group
iterated-product-∞-Group (cons x L) =
  product-∞-Group x (iterated-product-∞-Group L)
```

## Property

### The `type-∞-Group` of a iterated product of a `∞-Group` is the iterated product of the `type-∞-Group`

```agda
equiv-type-∞-Group-iterated-product-∞-Group :
  {l : Level} (L : list (∞-Group l))  →
  ( type-∞-Group (iterated-product-∞-Group L)) ≃
  ( iterated-product (map-list type-∞-Group L))
equiv-type-∞-Group-iterated-product-∞-Group {l} nil =
  equiv-is-contr
    ( is-proof-irrelevant-is-prop
        ( is-set-is-contr is-contr-raise-unit raise-star raise-star) refl )
    is-contr-raise-unit
equiv-type-∞-Group-iterated-product-∞-Group (cons G L) =
  ( ( equiv-prod id-equiv (equiv-type-∞-Group-iterated-product-∞-Group L )) ∘e
    ( ( equiv-type-∞-Group-product-∞-Group G (iterated-product-∞-Group L))))
```
