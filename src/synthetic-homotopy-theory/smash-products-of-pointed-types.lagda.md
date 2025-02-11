# Smash products of pointed types

```agda
module synthetic-homotopy-theory.smash-products-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
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
 A ∨∗ B ----> A ×∗ B
    |           |
    |           |
    ∨         ⌜ ∨
  unit -----> A ∧∗ B
```

where the map `A ∨∗ B → A ×∗ B` is the canonical inclusion
`map-wedge-product-Pointed-Type` from the
[wedge](synthetic-homotopy-theory.wedges-of-pointed-types.md) into the
[pointed cartesian product](structured-types.pointed-cartesian-product-types.md).

## Definition

```agda
smash-product-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
smash-product-Pointed-Type A B =
  pushout-Pointed-Type
    ( pointed-map-product-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))

infixr 15 _∧∗_
_∧∗_ = smash-product-Pointed-Type
```

**Note**: The symbols used for the smash product `_∧∗_` are the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` `\and`),
and the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input:
`\ast`), not the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
cogap-smash-product-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  cocone-Pointed-Type
    ( pointed-map-product-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B)) X →
  (A ∧∗ B) →∗ X
cogap-smash-product-Pointed-Type {A = A} {B} =
  cogap-Pointed-Type
    ( pointed-map-product-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))

map-cogap-smash-product-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  cocone-Pointed-Type
    ( pointed-map-product-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))
    ( X) →
  type-Pointed-Type (A ∧∗ B) → type-Pointed-Type X
map-cogap-smash-product-Pointed-Type c =
  pr1 (cogap-smash-product-Pointed-Type c)
```

## Properties

### The canonical pointed map from the cartesian product to the smash product

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-smash-product-product-Pointed-Type : (A ×∗ B) →∗ (A ∧∗ B)
  pointed-map-smash-product-product-Pointed-Type =
    inl-pushout-Pointed-Type
      ( pointed-map-product-wedge-Pointed-Type A B)
      ( terminal-pointed-map (A ∨∗ B))

  map-smash-product-product-Pointed-Type :
    type-Pointed-Type (A ×∗ B) → type-Pointed-Type (A ∧∗ B)
  map-smash-product-product-Pointed-Type =
    map-pointed-map pointed-map-smash-product-product-Pointed-Type
```

### Pointed maps into pointed types `A` and `B` induce a pointed map into `A ∧∗ B`

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {S : Pointed-Type l3}
  where

  gap-smash-product-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → S →∗ (A ∧∗ B)
  gap-smash-product-Pointed-Type f g =
    pointed-map-smash-product-product-Pointed-Type A B ∘∗
    gap-product-Pointed-Type f g

  map-gap-smash-product-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → type-Pointed-Type S → type-Pointed-Type (A ∧∗ B)
  map-gap-smash-product-Pointed-Type f g =
    pr1 (gap-smash-product-Pointed-Type f g)
```

### The canonical map from the wedge sum to the smash product identifies all points

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-smash-product-wedge-Pointed-Type : (A ∨∗ B) →∗ (A ∧∗ B)
  pointed-map-smash-product-wedge-Pointed-Type =
    pointed-map-smash-product-product-Pointed-Type A B ∘∗
    pointed-map-product-wedge-Pointed-Type A B

  map-smash-product-wedge-Pointed-Type :
    type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ∧∗ B)
  map-smash-product-wedge-Pointed-Type =
    map-pointed-map pointed-map-smash-product-wedge-Pointed-Type

  contraction-map-smash-product-wedge-Pointed-Type :
    ( x : type-Pointed-Type (A ∨∗ B)) →
    map-smash-product-wedge-Pointed-Type x ＝
    point-Pointed-Type (A ∧∗ B)
  contraction-map-smash-product-wedge-Pointed-Type x =
    ( glue-pushout
      ( map-product-wedge-Pointed-Type A B)
      ( map-pointed-map {A = A ∨∗ B} {B = unit-Pointed-Type}
        ( terminal-pointed-map (A ∨∗ B)))
      ( x)) ∙
    ( right-whisker-comp
      ( htpy-pointed-htpy
        ( is-initial-unit-Pointed-Type
          ( A ∧∗ B)
          ( inr-pushout-Pointed-Type
            ( pointed-map-product-wedge-Pointed-Type A B)
            ( terminal-pointed-map (A ∨∗ B)))))
      ( map-terminal-pointed-map (A ∨∗ B))
      ( x)) ∙
    ( preserves-point-pointed-map
      ( inclusion-point-Pointed-Type (A ∧∗ B)))

  coh-contraction-map-smash-product-wedge-Pointed-Type :
    ( ap
      ( map-smash-product-wedge-Pointed-Type)
      ( glue-wedge-Pointed-Type A B)) ∙
    ( contraction-map-smash-product-wedge-Pointed-Type
        ( map-inr-wedge-Pointed-Type A B (point-Pointed-Type B))) ＝
    ( contraction-map-smash-product-wedge-Pointed-Type
      ( map-inl-wedge-Pointed-Type A B (point-Pointed-Type A)))
  coh-contraction-map-smash-product-wedge-Pointed-Type =
    ( map-inv-compute-dependent-identification-eq-value-function
      ( map-smash-product-wedge-Pointed-Type)
      ( map-constant-pointed-map (A ∨∗ B) (A ∧∗ B))
      ( glue-wedge-Pointed-Type A B)
      ( contraction-map-smash-product-wedge-Pointed-Type
        ( map-inl-wedge-Pointed-Type A B (point-Pointed-Type A)))
      ( contraction-map-smash-product-wedge-Pointed-Type
        ( map-inr-wedge-Pointed-Type A B (point-Pointed-Type B)))
      ( apd
        ( contraction-map-smash-product-wedge-Pointed-Type)
        ( glue-wedge-Pointed-Type A B))) ∙
    ( left-whisker-concat
      ( contraction-map-smash-product-wedge-Pointed-Type
        ( map-inl-wedge-Pointed-Type A B (point-Pointed-Type A)))
      ( ap-const
        ( point-Pointed-Type (A ∧∗ B))
        ( glue-wedge-Pointed-Type A B))) ∙
    ( right-unit)
```

### The map from the pointed product to the smash product identifies elements

of the form `(x, b)` and `(a, y)`, where `b` and `a` are the base points of `B`
and `A` respectively.

```agda
module _
  {l1 l2 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  inl-glue-smash-product-Pointed-Type :
    ( x : type-Pointed-Type A) →
    map-smash-product-product-Pointed-Type A B
      ( x , point-Pointed-Type B) ＝
    map-smash-product-product-Pointed-Type A B
      ( point-Pointed-Type A , point-Pointed-Type B)
  inl-glue-smash-product-Pointed-Type x =
    ( ap
      ( map-smash-product-product-Pointed-Type A B)
      ( inv (compute-inl-product-wedge-Pointed-Type A B x))) ∙
    ( contraction-map-smash-product-wedge-Pointed-Type A B
      ( map-inl-wedge-Pointed-Type A B x))

  inr-glue-smash-product-Pointed-Type :
    ( y : type-Pointed-Type B) →
    map-smash-product-product-Pointed-Type A B
      ( point-Pointed-Type A , y) ＝
    map-smash-product-product-Pointed-Type A B
      ( point-Pointed-Type A , point-Pointed-Type B)
  inr-glue-smash-product-Pointed-Type y =
    ( ap
      ( map-smash-product-product-Pointed-Type A B)
      ( inv (compute-inr-product-wedge-Pointed-Type A B y))) ∙
    ( contraction-map-smash-product-wedge-Pointed-Type A B
      ( map-inr-wedge-Pointed-Type A B y))

  coh-glue-smash-product-Pointed-Type :
    inl-glue-smash-product-Pointed-Type (point-Pointed-Type A) ＝
    inr-glue-smash-product-Pointed-Type (point-Pointed-Type B)
  coh-glue-smash-product-Pointed-Type =
    ( left-whisker-concat
      ( ap
        ( map-smash-product-product-Pointed-Type A B)
        ( inv
          ( compute-inl-product-wedge-Pointed-Type A B (point-Pointed-Type A))))
      ( inv (coh-contraction-map-smash-product-wedge-Pointed-Type A B))) ∙
    ( inv
      ( assoc
        ( ap (map-smash-product-product-Pointed-Type A B)
          ( inv
            ( compute-inl-product-wedge-Pointed-Type A B
              ( point-Pointed-Type A))))
        ( ap (map-smash-product-wedge-Pointed-Type A B)
          ( glue-wedge-Pointed-Type A B))
        ( contraction-map-smash-product-wedge-Pointed-Type A B
          ( map-inr-wedge-Pointed-Type A B (point-Pointed-Type B))))) ∙
    ( right-whisker-concat
      ( ( left-whisker-concat
          ( ap (map-smash-product-product-Pointed-Type A B)
            ( inv
              ( compute-inl-product-wedge-Pointed-Type A B
                ( point-Pointed-Type A))))
          ( ap-comp
            ( map-smash-product-product-Pointed-Type A B)
            ( map-product-wedge-Pointed-Type A B)
            ( glue-wedge-Pointed-Type A B))) ∙
        ( inv
          ( ap-concat
            ( map-smash-product-product-Pointed-Type A B)
            ( inv
              ( compute-inl-product-wedge-Pointed-Type A B
                ( point-Pointed-Type A)))
            ( ap
              ( map-product-wedge-Pointed-Type A B)
              ( glue-wedge-Pointed-Type A B)))) ∙
        ( ap²
          ( map-smash-product-product-Pointed-Type A B)
          ( inv
            ( left-transpose-eq-concat
              ( compute-inl-product-wedge-Pointed-Type A B
                ( point-Pointed-Type A))
              ( inv
                ( compute-inr-product-wedge-Pointed-Type A B
                  ( point-Pointed-Type B)))
              ( ap
                ( map-product-wedge-Pointed-Type A B)
                ( glue-wedge-Pointed-Type A B))
              ( inv
                ( right-transpose-eq-concat
                  ( ap
                    ( map-product-wedge-Pointed-Type A B)
                    ( glue-wedge-Pointed-Type A B))
                  ( compute-inr-product-wedge-Pointed-Type A B
                    ( point-Pointed-Type B))
                  ( compute-inl-product-wedge-Pointed-Type A B
                    ( point-Pointed-Type A))
                  ( ( compute-glue-cogap
                      ( map-pointed-map
                        ( inclusion-point-Pointed-Type A))
                      ( map-pointed-map
                        ( inclusion-point-Pointed-Type B))
                      ( cocone-cocone-Pointed-Type
                        ( inclusion-point-Pointed-Type A)
                        ( inclusion-point-Pointed-Type B)
                        ( cocone-product-wedge-Pointed-Type A B))
                      ( point-Pointed-Type unit-Pointed-Type)) ∙
                    ( right-unit))))))))
      ( contraction-map-smash-product-wedge-Pointed-Type A B
        ( map-inr-wedge-Pointed-Type A B (point-Pointed-Type B))))
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

  map-map-universal-property-smash-product-Pointed-Type :
    type-Pointed-Type A → type-Pointed-Type B → type-Pointed-Type C
  map-map-universal-property-smash-product-Pointed-Type x y =
    map-pointed-map f (map-smash-product-product-Pointed-Type A B (x , y))

  preserves-point-map-map-universal-property-smash-product-Pointed-Type :
    (x : type-Pointed-Type A) →
    map-map-universal-property-smash-product-Pointed-Type x
      ( point-Pointed-Type B) ＝
    point-Pointed-Type C
  preserves-point-map-map-universal-property-smash-product-Pointed-Type x =
    ( ap
      ( map-pointed-map f)
      ( inl-glue-smash-product-Pointed-Type A B x)) ∙
    ( preserves-point-pointed-map f)

  map-universal-property-smash-product-Pointed-Type :
    type-Pointed-Type A → (B →∗ C)
  pr1 (map-universal-property-smash-product-Pointed-Type x) =
    map-map-universal-property-smash-product-Pointed-Type x
  pr2 (map-universal-property-smash-product-Pointed-Type x) =
    preserves-point-map-map-universal-property-smash-product-Pointed-Type x

  htpy-preserves-point-map-universal-property-smash-product-Pointed-Type :
    map-map-universal-property-smash-product-Pointed-Type
      ( point-Pointed-Type A) ~
    map-constant-pointed-map B C
  htpy-preserves-point-map-universal-property-smash-product-Pointed-Type y =
    ( ap (map-pointed-map f) (inr-glue-smash-product-Pointed-Type A B y)) ∙
    ( preserves-point-pointed-map f)

  coherence-point-preserves-point-map-universal-property-smash-product-Pointed-Type :
    coherence-point-unpointed-htpy-pointed-Π
      ( map-universal-property-smash-product-Pointed-Type
        ( point-Pointed-Type A))
      ( constant-pointed-map B C)
      ( htpy-preserves-point-map-universal-property-smash-product-Pointed-Type)
  coherence-point-preserves-point-map-universal-property-smash-product-Pointed-Type =
    ( right-whisker-concat
      ( ap²
        ( map-pointed-map f)
        ( coh-glue-smash-product-Pointed-Type A B))
      ( preserves-point-pointed-map f)) ∙
    ( inv right-unit)

  pointed-htpy-preserves-point-map-universal-property-smash-product-Pointed-Type :
    map-universal-property-smash-product-Pointed-Type (point-Pointed-Type A) ~∗
    constant-pointed-map B C
  pr1
    pointed-htpy-preserves-point-map-universal-property-smash-product-Pointed-Type =
    htpy-preserves-point-map-universal-property-smash-product-Pointed-Type
  pr2
    pointed-htpy-preserves-point-map-universal-property-smash-product-Pointed-Type =
    coherence-point-preserves-point-map-universal-property-smash-product-Pointed-Type

  preserves-point-map-universal-property-smash-product-Pointed-Type :
    map-universal-property-smash-product-Pointed-Type (point-Pointed-Type A) ＝
    constant-pointed-map B C
  preserves-point-map-universal-property-smash-product-Pointed-Type =
    eq-pointed-htpy
      ( map-universal-property-smash-product-Pointed-Type
        ( point-Pointed-Type A))
      ( constant-pointed-map B C)
      ( pointed-htpy-preserves-point-map-universal-property-smash-product-Pointed-Type)

  pointed-map-universal-property-smash-product-Pointed-Type :
    A →∗ (pointed-map-Pointed-Type B C)
  pr1 pointed-map-universal-property-smash-product-Pointed-Type =
    map-universal-property-smash-product-Pointed-Type
  pr2 pointed-map-universal-property-smash-product-Pointed-Type =
    preserves-point-map-universal-property-smash-product-Pointed-Type
```

## See also

- [Wedges of pointed types](synthetic-homotopy-theory.wedges-of-pointed-types.md)
