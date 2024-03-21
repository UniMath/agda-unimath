# Smash products of pointed types

```agda
module synthetic-homotopy-theory.smash-products-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import structured-types.constant-pointed-maps
open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-span-diagrams
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagrams
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.pushouts-of-pointed-types
open import synthetic-homotopy-theory.wedges-of-pointed-types
```

</details>

## Idea

Given two [pointed types](structured-types.pointed-types.md) `a : A` and `b : B`
we may form their **smash product** as the following
[pushout](synthetic-homotopy-theory.pushouts.md)

```text
 A ∨∗ B -----> unit
    |           |
    |           |
    v        ⌜  v
  A ×∗ B --> A ∧∗ B
```

where the map `A ∨∗ B → A ×∗ B` is the canonical inclusion
`pointed-map-product-pointed-wedge` from the
[wedge](synthetic-homotopy-theory.wedges-of-pointed-types.md) into the
[pointed cartesian product](structured-types.pointed-cartesian-product-types.md).

## Definition

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-span-diagram-smash-product :
    pointed-span-diagram (l1 ⊔ l2) lzero (l1 ⊔ l2)
  pointed-span-diagram-smash-product =
    make-pointed-span-diagram
      ( pointed-map-product-pointed-wedge A B)
      ( terminal-pointed-map (A ∨∗ B))

  smash-product : Pointed-Type (l1 ⊔ l2)
  smash-product = standard-pointed-pushout pointed-span-diagram-smash-product

  infixr 15 _∧∗_
  _∧∗_ = smash-product
```

**Note**: The symbols used for the smash product `_∧∗_` are the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` `\and`),
and the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input:
`\ast`), not the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3}
  where


  cogap-smash-product-Pointed-Type :
    cocone-pointed-span-diagram (pointed-span-diagram-smash-product A B) X →
    (A ∧∗ B) →∗ X
  cogap-smash-product-Pointed-Type =
    cogap-cocone-pointed-span-diagram
      ( pointed-span-diagram-smash-product A B)

  map-cogap-smash-product-Pointed-Type :
    cocone-pointed-span-diagram (pointed-span-diagram-smash-product A B) X →
    type-Pointed-Type (A ∧∗ B) → type-Pointed-Type X
  map-cogap-smash-product-Pointed-Type c =
    map-pointed-map (cogap-smash-product-Pointed-Type c)
```

## Properties

### The canonical pointed map from the cartesian product to the smash product

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-smash-product-product : (A ×∗ B) →∗ (A ∧∗ B)
  pointed-map-smash-product-product =
    inl-standard-pointed-pushout (pointed-span-diagram-smash-product A B)

  map-smash-product-product :
    type-Pointed-Type (A ×∗ B) → type-Pointed-Type (A ∧∗ B)
  map-smash-product-product =
    map-pointed-map pointed-map-smash-product-product
```

### Pointed maps into pointed types `A` and `B` induce a pointed map into `A ∧∗ B`

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {S : Pointed-Type l3}
  where

  gap-smash-product :
    (f : S →∗ A) (g : S →∗ B) → S →∗ (A ∧∗ B)
  gap-smash-product f g =
    pointed-map-smash-product-product A B ∘∗
    gap-product-Pointed-Type f g

  map-gap-smash-product :
    (f : S →∗ A) (g : S →∗ B) → type-Pointed-Type S → type-Pointed-Type (A ∧∗ B)
  map-gap-smash-product f g =
    map-pointed-map (gap-smash-product f g)
```

### The canonical map from the wedge sum to the smash product identifies all points

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-smash-product-pointed-wedge : (A ∨∗ B) →∗ (A ∧∗ B)
  pointed-map-smash-product-pointed-wedge =
    pointed-map-smash-product-product A B ∘∗
    pointed-map-product-pointed-wedge A B

  map-smash-product-pointed-wedge :
    type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ∧∗ B)
  map-smash-product-pointed-wedge =
    map-pointed-map pointed-map-smash-product-pointed-wedge

  contraction-map-smash-product-pointed-wedge :
    (x : type-Pointed-Type (A ∨∗ B)) →
    map-smash-product-pointed-wedge x ＝
    point-Pointed-Type (A ∧∗ B)
  contraction-map-smash-product-pointed-wedge x =
    ( glue-standard-pushout
      ( span-diagram-pointed-span-diagram
        ( pointed-span-diagram-smash-product A B))
      ( x)) ∙
    ( right-whisker-comp
      ( htpy-pointed-htpy
        ( is-initial-unit-Pointed-Type
          (A ∧∗ B)
          ( inr-standard-pointed-pushout
            ( pointed-span-diagram-smash-product A B))))
      ( map-terminal-pointed-map (A ∨∗ B))
      ( x)) ∙
    ( preserves-point-pointed-map
      ( inclusion-point-Pointed-Type (A ∧∗ B)))

  coh-contraction-map-smash-product-pointed-wedge :
    coherence-triangle-identifications'
      ( contraction-map-smash-product-pointed-wedge
        ( map-inl-pointed-wedge A B (point-Pointed-Type A)))
      ( contraction-map-smash-product-pointed-wedge
        ( map-inr-pointed-wedge A B (point-Pointed-Type B)))
      ( ap
        ( map-smash-product-pointed-wedge)
        ( glue-pointed-wedge A B))
  coh-contraction-map-smash-product-pointed-wedge =
    ( map-inv-compute-dependent-identification-eq-value-function
      ( map-smash-product-pointed-wedge)
      ( map-constant-pointed-map (A ∨∗ B) (A ∧∗ B))
      ( glue-pointed-wedge A B)
      ( contraction-map-smash-product-pointed-wedge
        ( map-inl-pointed-wedge A B (point-Pointed-Type A)))
      ( contraction-map-smash-product-pointed-wedge
        ( map-inr-pointed-wedge A B (point-Pointed-Type B)))
      ( apd
        ( contraction-map-smash-product-pointed-wedge)
        ( glue-pointed-wedge A B))) ∙
    left-whisker-concat
      ( contraction-map-smash-product-pointed-wedge
        ( map-inl-pointed-wedge A B (point-Pointed-Type A)))
      ( ap-const
        ( point-Pointed-Type (A ∧∗ B))
        ( glue-pointed-wedge A B)) ∙
    ( right-unit)
```

### The map from the pointed product to the smash product identifies elements of the form `(x, b)` and `(a, y)`, where `b` and `a` are the base points of `B` and `A` respectively.

```agda
module _
  {l1 l2 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  inl-glue-smash-product :
    ( x : type-Pointed-Type A) →
    map-smash-product-product A B
      ( x , point-Pointed-Type B) ＝
    map-smash-product-product A B
      ( point-Pointed-Type A , point-Pointed-Type B)
  inl-glue-smash-product x =
    ( ap
      ( map-smash-product-product A B)
      ( inv (compute-inl-product-pointed-wedge A B x))) ∙
    ( contraction-map-smash-product-pointed-wedge A B
      ( map-inl-pointed-wedge A B x))

  inr-glue-smash-product :
    ( y : type-Pointed-Type B) →
    map-smash-product-product A B
      ( point-Pointed-Type A , y) ＝
    map-smash-product-product A B
      ( point-Pointed-Type A , point-Pointed-Type B)
  inr-glue-smash-product y =
    ( ap
      ( map-smash-product-product A B)
      ( inv (compute-inr-product-pointed-wedge A B y))) ∙
    ( contraction-map-smash-product-pointed-wedge A B
      ( map-inr-pointed-wedge A B y))

  coh-glue-smash-product :
    inl-glue-smash-product (point-Pointed-Type A) ＝
    inr-glue-smash-product (point-Pointed-Type B)
  coh-glue-smash-product =
    ( left-whisker-concat
      ( ap
        ( map-smash-product-product A B)
        ( inv
          ( compute-inl-product-pointed-wedge A B (point-Pointed-Type A))))
      ( inv (coh-contraction-map-smash-product-pointed-wedge A B))) ∙
    ( inv
      ( assoc
        ( ap (map-smash-product-product A B)
          ( inv
            ( compute-inl-product-pointed-wedge A B
              ( point-Pointed-Type A))))
        ( ap (map-smash-product-pointed-wedge A B)
          ( glue-pointed-wedge A B))
        ( contraction-map-smash-product-pointed-wedge A B
          ( map-inr-pointed-wedge A B (point-Pointed-Type B))))) ∙
    ( right-whisker-concat
      ( ( left-whisker-concat
          ( ap (map-smash-product-product A B)
            ( inv
              ( compute-inl-product-pointed-wedge A B
                ( point-Pointed-Type A))))
          ( ap-comp
            ( map-smash-product-product A B)
            ( map-product-pointed-wedge A B)
            ( glue-pointed-wedge A B))) ∙
        ( inv
          ( ap-concat
            ( map-smash-product-product A B)
            ( inv
              ( compute-inl-product-pointed-wedge A B
                ( point-Pointed-Type A)))
            ( ap
              ( map-product-pointed-wedge A B)
              ( glue-pointed-wedge A B)))) ∙
        ( ap²
          ( map-smash-product-product A B)
          ( inv
            ( left-transpose-eq-concat
              ( compute-inl-product-pointed-wedge A B
                ( point-Pointed-Type A))
              ( inv
                ( compute-inr-product-pointed-wedge A B
                  ( point-Pointed-Type B)))
              ( ap
                ( map-product-pointed-wedge A B)
                ( glue-pointed-wedge A B))
              ( inv
                ( right-transpose-eq-concat
                  ( ap
                    ( map-product-pointed-wedge A B)
                    ( glue-pointed-wedge A B))
                  ( compute-inr-product-pointed-wedge A B
                    ( point-Pointed-Type B))
                  ( compute-inl-product-pointed-wedge A B
                    ( point-Pointed-Type A))
                  ( ( compute-glue-cogap-cocone-span-diagram
                      ( span-diagram-pointed-span-diagram
                        ( pointed-span-diagram-pointed-wedge A B))
                      ( cocone-cocone-pointed-span-diagram
                        ( pointed-span-diagram-pointed-wedge A B)
                        ( cocone-product-pointed-wedge A B))
                      ( point-Pointed-Type unit-Pointed-Type)) ∙
                    ( right-unit))))))))
      ( contraction-map-smash-product-pointed-wedge A B
        ( map-inr-pointed-wedge A B (point-Pointed-Type B))))
```

### The universal property of the smash product

Fixing a pointed type `B`, the _universal property of the smash product_ states
that the functor `- ∧∗ B` forms the left-adjoint to the functor `B →∗ -` of
[pointed maps](structured-types.pointed-maps.md) with source `B`. In the
language of type theory, this means that we have a pointed equivalence:

```text
  ((A ∧∗ B) →∗ C) ≃∗ (A →∗ B →∗ C).
```

**Note:** The categorical product in the category of pointed types is the
[pointed cartesian product](structured-types.pointed-cartesian-product-types.md).

```agda
module _
  {l1 l2 l3 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) (C : Pointed-Type l3)
  (f : (A ∧∗ B) →∗ C)
  where

  map-map-universal-property-smash-product :
    type-Pointed-Type A → type-Pointed-Type B → type-Pointed-Type C
  map-map-universal-property-smash-product x y =
    map-pointed-map f (map-smash-product-product A B (x , y))

  preserves-point-map-map-universal-property-smash-product :
    (x : type-Pointed-Type A) →
    map-map-universal-property-smash-product x (point-Pointed-Type B) ＝
    point-Pointed-Type C
  preserves-point-map-map-universal-property-smash-product x =
    ( ap (map-pointed-map f) (inl-glue-smash-product A B x)) ∙
    ( preserves-point-pointed-map f)

  map-universal-property-smash-product :
    type-Pointed-Type A → (B →∗ C)
  pr1 (map-universal-property-smash-product x) =
    map-map-universal-property-smash-product x
  pr2 (map-universal-property-smash-product x) =
    preserves-point-map-map-universal-property-smash-product x

  htpy-preserves-point-map-universal-property-smash-product :
    (y : type-Pointed-Type B) →
    map-map-universal-property-smash-product (point-Pointed-Type A) y ＝
    point-Pointed-Type C
  htpy-preserves-point-map-universal-property-smash-product y =
    ( ap (map-pointed-map f) (inr-glue-smash-product A B y)) ∙
    ( preserves-point-pointed-map f)

  coherence-point-preserves-point-map-universal-property-smash-product :
    coherence-point-unpointed-htpy-pointed-Π
      ( map-universal-property-smash-product (point-Pointed-Type A))
      ( constant-pointed-map B C)
      ( htpy-preserves-point-map-universal-property-smash-product)
  coherence-point-preserves-point-map-universal-property-smash-product =
    ( right-whisker-concat
      ( ap²
        ( map-pointed-map f)
        ( coh-glue-smash-product A B))
      ( preserves-point-pointed-map f)) ∙
    ( inv right-unit)

  pointed-htpy-preserves-point-map-universal-property-smash-product :
    map-universal-property-smash-product (point-Pointed-Type A) ~∗
    constant-pointed-map B C
  pr1 pointed-htpy-preserves-point-map-universal-property-smash-product =
    htpy-preserves-point-map-universal-property-smash-product
  pr2 pointed-htpy-preserves-point-map-universal-property-smash-product =
    coherence-point-preserves-point-map-universal-property-smash-product

  preserves-point-map-universal-property-smash-product :
    map-universal-property-smash-product (point-Pointed-Type A) ＝
    constant-pointed-map B C
  preserves-point-map-universal-property-smash-product =
    eq-pointed-htpy
      ( map-universal-property-smash-product
        ( point-Pointed-Type A))
      ( constant-pointed-map B C)
      ( pointed-htpy-preserves-point-map-universal-property-smash-product)

  pointed-map-universal-property-smash-product :
    A →∗ (pointed-map-Pointed-Type B C)
  pr1 pointed-map-universal-property-smash-product =
    map-universal-property-smash-product
  pr2 pointed-map-universal-property-smash-product =
    preserves-point-map-universal-property-smash-product
```

## See also

- [Wedges of pointed types](synthetic-homotopy-theory.wedges-of-pointed-types.md)
