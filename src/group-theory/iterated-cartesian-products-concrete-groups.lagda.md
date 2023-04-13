# Iterated cartesian products of concrete groups

```agda
module group-theory.iterated-cartesian-products-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.iterated-cartesian-product-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.cartesian-products-concrete-groups
open import group-theory.concrete-groups
open import group-theory.groups

open import higher-group-theory.higher-groups
open import higher-group-theory.iterated-cartesian-products-higher-groups

open import lists.functoriality-lists
open import lists.lists

open import structured-types.pointed-types
```

</details>

## Definition

```agda
iterated-product-Concrete-Group :
  {l : Level} → (L : list (Concrete-Group l)) → Concrete-Group l
iterated-product-Concrete-Group nil = unit-type-Concrete-Group
iterated-product-Concrete-Group (cons G L) =
  product-Concrete-Group G (iterated-product-Concrete-Group L)
```

## Property

```agda
equiv-type-Concrete-group-iterated-product-Concrete-Group :
  {l : Level} → (L : list (Concrete-Group l)) →
  ( type-Concrete-Group (iterated-product-Concrete-Group L)) ≃
  ( iterated-product (map-list type-Concrete-Group L))
equiv-type-Concrete-group-iterated-product-Concrete-Group nil =
  equiv-is-contr
    ( is-proof-irrelevant-is-prop
        ( is-set-is-contr is-contr-raise-unit raise-star raise-star) refl )
    is-contr-raise-unit
equiv-type-Concrete-group-iterated-product-Concrete-Group (cons G L) =
  equiv-prod
    ( id-equiv)
    ( equiv-type-Concrete-group-iterated-product-Concrete-Group L) ∘e
  equiv-type-Concrete-Group-produt-Concrete-Group
    ( G)
    ( iterated-product-Concrete-Group L)
```
