# Wedges of types

```agda
module synthetic-homotopy-theory.wedges-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.cofibers
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

The **wedge** or **wedge sum** of two pointed types `a : A` and `b : B` is
defined by the following pushout.

```md
  unit ------> A
    |          |
    |          |
    v       ⌜  v
    B -----> A ∨* B
```

The wedge sum is canonically pointed at the (identified) images of `a` and `b`.

## Definition

```agda
_∨*_ :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
pr1 (A ∨* B) =
  pushout
    { S = unit}
    ( λ _ → point-Pointed-Type A)
    ( λ _ → point-Pointed-Type B)
pr2 (A ∨* B) =
  inl-pushout
    ( λ _ → point-Pointed-Type A)
    ( λ _ → point-Pointed-Type B)
    ( point-Pointed-Type A)

indexed-wedge :
  {l1 l2 : Level} (I : UU l1) (A : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
pr1 (indexed-wedge I A) = cofiber (λ i → i , point-Pointed-Type (A i))
pr2 (indexed-wedge I A) = pt-cofiber (λ i → i , point-Pointed-Type (A i))
```

## Properties

### The canonical inclusion of the wedge sum `A ∨* B` into the pointed product `A ×* B`

There is a canonical inclusion of the wedge sum into the pointed product that is
defined by the cogap map induced by the canonical inclusions `A → A ×* B ← B`.

```agda
cocone-prod-wedge-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  cocone
    { S = unit}
    ( λ _ → point-Pointed-Type A)
    ( λ _ → point-Pointed-Type B)
    ( type-Pointed-Type (A ×* B))
pr1 (cocone-prod-wedge-Pointed-Type A B) x = x , point-Pointed-Type B
pr1 (pr2 (cocone-prod-wedge-Pointed-Type A B)) y = point-Pointed-Type A , y
pr2 (pr2 (cocone-prod-wedge-Pointed-Type A B)) = refl-htpy

map-prod-wedge-Pointed-Type :
  {l1 l2 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) →
  type-Pointed-Type (A ∨* B) → type-Pointed-Type (A ×* B)
map-prod-wedge-Pointed-Type A B =
  cogap
    ( λ _ → point-Pointed-Type A)
    ( λ _ → point-Pointed-Type B)
    ( cocone-prod-wedge-Pointed-Type A B)

pointed-map-prod-wedge-Pointed-Type :
  {l1 l2 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A ∨* B) →* (A ×* B)
pr1 (pointed-map-prod-wedge-Pointed-Type A B) =
  map-prod-wedge-Pointed-Type A B
pr2 (pointed-map-prod-wedge-Pointed-Type A B) =
  compute-inl-cogap
    ( λ _ → point-Pointed-Type A)
    ( λ _ → point-Pointed-Type B)
    ( cocone-prod-wedge-Pointed-Type A B)
    ( point-Pointed-Type A)
```

## See also

- [Smash products of pointed types](synthetic-homotopy-theory.smash-products-of-pointed-types.md)
  for a related construction.
