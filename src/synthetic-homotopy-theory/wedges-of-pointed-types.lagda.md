# Wedges of pointed types

```agda
module synthetic-homotopy-theory.wedges-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
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
defined by the following pointed pushout:

```text
  unit ------> A
    |          |
    |          |
    v       ⌜  v
    B -----> A ∨∗ B,
```

and is thus canonically pointed at the identified image of `a` and `b`.

## Definition

```agda
wedge-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
wedge-Pointed-Type A B =
  pushout-Pointed-Type
    ( inclusion-point-Pointed-Type A)
    ( inclusion-point-Pointed-Type B)

_∨∗_ = wedge-Pointed-Type
```

**Note**: the symbols used for the wedge sum `_∨∗_` are the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`) and
the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`),
not the [latin small letter v](https://codepoints.net/U+0076) `v` or the
[asterisk](https://codepoints.net/U+002A) `*`.

```agda
indexed-wedge :
  {l1 l2 : Level} (I : UU l1) (A : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
pr1 (indexed-wedge I A) = cofiber (λ i → i , point-Pointed-Type (A i))
pr2 (indexed-wedge I A) = point-cofiber (λ i → i , point-Pointed-Type (A i))
```

## Properties

### The inclusion of the wedge sum `A ∨∗ B` into the pointed product `A ×∗ B`

There is a canonical inclusion of the wedge sum into the pointed product that is
defined by the cogap map induced by the canonical inclusions `A → A ×∗ B ← B`.

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  cocone-prod-wedge-Pointed-Type :
    type-cocone-Pointed-Type
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)
      ( A ×∗ B)
  pr1 cocone-prod-wedge-Pointed-Type = inl-prod-Pointed-Type A B
  pr1 (pr2 cocone-prod-wedge-Pointed-Type) = inr-prod-Pointed-Type A B
  pr1 (pr2 (pr2 cocone-prod-wedge-Pointed-Type)) = refl-htpy
  pr2 (pr2 (pr2 cocone-prod-wedge-Pointed-Type)) = refl

  pointed-map-prod-wedge-Pointed-Type :
    (A ∨∗ B) →∗ (A ×∗ B)
  pointed-map-prod-wedge-Pointed-Type =
    cogap-Pointed-Type
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)
      ( cocone-prod-wedge-Pointed-Type)

  map-prod-wedge-Pointed-Type :
    type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ×∗ B)
  map-prod-wedge-Pointed-Type = pr1 pointed-map-prod-wedge-Pointed-Type
```

## See also

- [Smash products of pointed types](synthetic-homotopy-theory.smash-products-of-pointed-types.md)
  for a related construction.
