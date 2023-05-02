# Wedges of types

```agda
module synthetic-homotopy-theory.wedges-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.universe-levels

open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-spans-of-pointed-types
open import synthetic-homotopy-theory.cofibers
open import synthetic-homotopy-theory.pushouts-of-pointed-types
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
A ∨* B =
  pushout-Pointed-Type
    ( cogap-pointed-unit A)
    ( cogap-pointed-unit B)

indexed-wedge :
  {l1 l2 : Level} (I : UU l1) (A : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
pr1 (indexed-wedge I A) = cofiber (λ i → i , point-Pointed-Type (A i))
pr2 (indexed-wedge I A) = point-cofiber (λ i → i , point-Pointed-Type (A i))
```

## Properties

### The canonical inclusion of the wedge sum `A ∨* B` into the pointed product `A ×* B`

There is a canonical inclusion of the wedge sum into the pointed product that is
defined by the cogap map induced by the canonical inclusions `A → A ×* B ← B`.

```agda
cocone-prod-wedge-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  type-cocone-Pointed-Type
    ( cogap-pointed-unit A)
    ( cogap-pointed-unit B)
    ( A ×* B)
pr1 (cocone-prod-wedge-Pointed-Type A B) = inl-prod-Pointed-Type A B
pr1 (pr2 (cocone-prod-wedge-Pointed-Type A B)) = inr-prod-Pointed-Type A B
pr2 (pr2 (cocone-prod-wedge-Pointed-Type A B)) = refl-htpy

pointed-map-prod-wedge-Pointed-Type :
  {l1 l2 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A ∨* B) →* (A ×* B)
pointed-map-prod-wedge-Pointed-Type A B =
  cogap-Pointed-Type
    ( cogap-pointed-unit A)
    ( cogap-pointed-unit B)
    ( cocone-prod-wedge-Pointed-Type A B)

map-prod-wedge-Pointed-Type :
  {l1 l2 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) →
  type-Pointed-Type (A ∨* B) → type-Pointed-Type (A ×* B)
map-prod-wedge-Pointed-Type A B = pr1 (pointed-map-prod-wedge-Pointed-Type A B)
```

## See also

- [Smash products of pointed types](synthetic-homotopy-theory.smash-products-of-pointed-types.md)
  for a related construction.
