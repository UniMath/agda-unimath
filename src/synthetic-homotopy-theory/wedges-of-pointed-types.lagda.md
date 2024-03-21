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
open import structured-types.pointed-span-diagrams
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagrams
open import synthetic-homotopy-theory.cofibers
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.pushouts-of-pointed-types
```

</details>

## Idea

The **wedge** or **wedge sum** of two
[pointed types](structured-types.pointed-types.md) `a : A` and `b : B` is
defined by the following
[pointed pushout](synthetic-homotopy-theory.pushouts-of-pointed-types.md):

```text
  unit ------> B
    |          |
    |          |
    v        ⌜ v
    A -----> A ∨∗ B,
```

and is thus canonically pointed at the identified image of `a` and `b`.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-span-diagram-pointed-wedge : pointed-span-diagram l1 l2 lzero
  pointed-span-diagram-pointed-wedge =
    make-pointed-span-diagram
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-wedge : Pointed-Type (l1 ⊔ l2)
  pointed-wedge =
    standard-pointed-pushout (pointed-span-diagram-pointed-wedge A B)

  infixr 10 _∨∗_
  _∨∗_ = pointed-wedge

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  inl-pointed-wedge : A →∗ (A ∨∗ B)
  inl-pointed-wedge =
    inl-standard-pointed-pushout
      ( pointed-span-diagram-pointed-wedge A B)

  map-inl-pointed-wedge :
    type-Pointed-Type A → type-Pointed-Type (A ∨∗ B)
  map-inl-pointed-wedge =
    map-pointed-map inl-pointed-wedge

  inr-pointed-wedge : B →∗ A ∨∗ B
  inr-pointed-wedge =
    inr-standard-pointed-pushout
      ( pointed-span-diagram-pointed-wedge A B)

  map-inr-pointed-wedge :
    type-Pointed-Type B → type-Pointed-Type (A ∨∗ B)
  map-inr-pointed-wedge =
    map-pointed-map inr-pointed-wedge

indexed-pointed-wedge :
  {l1 l2 : Level} (I : UU l1) (A : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
pr1 (indexed-pointed-wedge I A) =
  cofiber (λ i → (i , point-Pointed-Type (A i)))
pr2 (indexed-pointed-wedge I A) =
  point-cofiber (λ i → (i , point-Pointed-Type (A i)))

⋁∗ = indexed-pointed-wedge
```

**Note**: the symbols used for the wedge sum `_∨∗_` are the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`) and
the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`),
not the [latin small letter v](https://codepoints.net/U+0076) `v` or the
[asterisk](https://codepoints.net/U+002A) `*`. The `⋁` symbol used for the
indexed wedge sum, `⋁∗`, is the
[N-ary logical or](https://codepoints.net/U+22C1) (agda-input: `\bigvee`).

## Properties

### The images of the base points `a : A` and `b : B` are identified in `A ∨∗ B`

```agda
glue-pointed-wedge :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  map-inl-pointed-wedge A B (point-Pointed-Type A) ＝
  map-inr-pointed-wedge A B (point-Pointed-Type B)
glue-pointed-wedge A B =
  glue-standard-pushout
    ( span-diagram-pointed-span-diagram
      ( pointed-span-diagram-pointed-wedge A B))
    ( point-Pointed-Type unit-Pointed-Type)
```

### The inclusion of the wedge sum `A ∨∗ B` into the pointed product `A ×∗ B`

There is a canonical inclusion of the wedge sum into the pointed product that is
defined by the cogap map induced by the canonical inclusions `A → A ×∗ B ← B`.

Elements of the form `(x, b)` and `(a, y)`, where `b` and `a` are basepoints,
lie in the image of the inclusion of the wedge sum into the pointed product.

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  cocone-product-pointed-wedge :
    cocone-pointed-span-diagram
      ( pointed-span-diagram-pointed-wedge A B)
      ( A ×∗ B)
  pr1 cocone-product-pointed-wedge = inl-product-Pointed-Type A B
  pr1 (pr2 cocone-product-pointed-wedge) = inr-product-Pointed-Type A B
  pr1 (pr2 (pr2 cocone-product-pointed-wedge)) = refl-htpy
  pr2 (pr2 (pr2 cocone-product-pointed-wedge)) = refl

  pointed-map-product-pointed-wedge :
    (A ∨∗ B) →∗ (A ×∗ B)
  pointed-map-product-pointed-wedge =
    cogap-cocone-pointed-span-diagram
      ( pointed-span-diagram-pointed-wedge A B)
      ( cocone-product-pointed-wedge)

  map-product-pointed-wedge :
    type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ×∗ B)
  map-product-pointed-wedge = map-pointed-map pointed-map-product-pointed-wedge

  compute-inl-product-pointed-wedge :
    ( x : type-Pointed-Type A) →
    ( map-product-pointed-wedge (map-inl-pointed-wedge A B x)) ＝
    ( x , point-Pointed-Type B)
  compute-inl-product-pointed-wedge =
    htpy-compute-inl-cogap-cocone-pointed-span-diagram
      ( pointed-span-diagram-pointed-wedge A B)
      ( cocone-product-pointed-wedge)

  compute-inr-product-pointed-wedge :
    ( y : type-Pointed-Type B) →
    ( map-product-pointed-wedge (map-inr-pointed-wedge A B y)) ＝
    ( point-Pointed-Type A , y)
  compute-inr-product-pointed-wedge =
    htpy-compute-inr-cogap-cocone-pointed-span-diagram
      ( pointed-span-diagram-pointed-wedge A B)
      ( cocone-product-pointed-wedge)
```

## See also

- [Smash products of pointed types](synthetic-homotopy-theory.smash-products-of-pointed-types.md)
  for a related construction.
