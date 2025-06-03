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
open import synthetic-homotopy-theory.cofibers-of-maps
open import synthetic-homotopy-theory.cofibers-of-pointed-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.pushouts-of-pointed-types
open import synthetic-homotopy-theory.wedges-of-pointed-types
```

</details>

## Idea

Given two [pointed types](structured-types.pointed-types.md) `a : A` and `b : B`
we may form their
{{#concept "smash product" Disambiguation="of pointed types" WD="smash product" WDID=Q2295009 Agda=smash-Pointed-Type}}
`A ∧∗ B` as the [cofiber](synthetic-homotopy-theory.cofibers-of-pointed-maps.md)
of the canonical inclusion `A ∨∗ B →∗ A ×∗ B` from the
[wedge](synthetic-homotopy-theory.wedges-of-pointed-types.md) into the
[pointed cartesian product](structured-types.pointed-cartesian-product-types.md).
In other words, the smash product `A ∧∗ B` is the
[pushout](synthetic-homotopy-theory.pushouts-of-pointed-types.md) of pointed
types

```text
  A ∨∗ B ----> A ×∗ B
    |            |
    |            |
    ∨          ⌜ ∨
    * -------> A ∧∗ B.
```

## Definition

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  smash-Pointed-Type : Pointed-Type (l1 ⊔ l2)
  smash-Pointed-Type =
    cofiber-Pointed-Type (pointed-map-product-wedge-Pointed-Type A B)

  infixr 15 _∧∗_
  _∧∗_ : Pointed-Type (l1 ⊔ l2)
  _∧∗_ = smash-Pointed-Type
```

**Note**: The symbols used for the smash product `_∧∗_` are the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` `\and`),
and the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input:
`\ast`), not the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
cogap-smash-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  cocone-Pointed-Type
    ( pointed-map-product-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B)) X →
  (A ∧∗ B) →∗ X
cogap-smash-Pointed-Type {A = A} {B} =
  cogap-cofiber-Pointed-Type (pointed-map-product-wedge-Pointed-Type A B)

map-cogap-smash-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  cocone-Pointed-Type
    ( pointed-map-product-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))
    ( X) →
  type-Pointed-Type (A ∧∗ B) → type-Pointed-Type X
map-cogap-smash-Pointed-Type {A = A} {B} =
  map-cogap-cofiber-Pointed-Type (pointed-map-product-wedge-Pointed-Type A B)
```

## Properties

### The canonical pointed map from the cartesian product to the smash product

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-smash-product-product-Pointed-Type : (A ×∗ B) →∗ (A ∧∗ B)
  pointed-map-smash-product-product-Pointed-Type =
    inl-cofiber-Pointed-Type
      ( pointed-map-product-wedge-Pointed-Type A B)

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

  gap-smash-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → S →∗ (A ∧∗ B)
  gap-smash-Pointed-Type f g =
    pointed-map-smash-product-product-Pointed-Type A B ∘∗
    gap-product-Pointed-Type f g

  map-gap-smash-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → type-Pointed-Type S → type-Pointed-Type (A ∧∗ B)
  map-gap-smash-Pointed-Type f g =
    pr1 (gap-smash-Pointed-Type f g)
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
          ( inr-cofiber-Pointed-Type
            ( pointed-map-product-wedge-Pointed-Type A B))))
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
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  inl-glue-smash-Pointed-Type :
    ( x : type-Pointed-Type A) →
    map-smash-product-product-Pointed-Type A B
      ( x , point-Pointed-Type B) ＝
    map-smash-product-product-Pointed-Type A B
      ( point-Pointed-Type A , point-Pointed-Type B)
  inl-glue-smash-Pointed-Type x =
    ( ap
      ( map-smash-product-product-Pointed-Type A B)
      ( inv (compute-inl-product-wedge-Pointed-Type A B x))) ∙
    ( contraction-map-smash-product-wedge-Pointed-Type A B
      ( map-inl-wedge-Pointed-Type A B x))

  inr-glue-smash-Pointed-Type :
    ( y : type-Pointed-Type B) →
    map-smash-product-product-Pointed-Type A B
      ( point-Pointed-Type A , y) ＝
    map-smash-product-product-Pointed-Type A B
      ( point-Pointed-Type A , point-Pointed-Type B)
  inr-glue-smash-Pointed-Type y =
    ( ap
      ( map-smash-product-product-Pointed-Type A B)
      ( inv (compute-inr-product-wedge-Pointed-Type A B y))) ∙
    ( contraction-map-smash-product-wedge-Pointed-Type A B
      ( map-inr-wedge-Pointed-Type A B y))

  coh-glue-smash-Pointed-Type :
    inl-glue-smash-Pointed-Type (point-Pointed-Type A) ＝
    inr-glue-smash-Pointed-Type (point-Pointed-Type B)
  coh-glue-smash-Pointed-Type =
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
  ((A ∧∗ B) →∗ C) ≃∗ (A →∗ (B →∗ C)).
```

**Note:** The categorical product in the category of pointed types is the
[pointed cartesian product](structured-types.pointed-cartesian-product-types.md).

```agda
module _
  {l1 l2 l3 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) (C : Pointed-Type l3)
  (f : (A ∧∗ B) →∗ C)
  where

  map-map-universal-property-smash-Pointed-Type :
    type-Pointed-Type A → type-Pointed-Type B → type-Pointed-Type C
  map-map-universal-property-smash-Pointed-Type x y =
    map-pointed-map f (map-smash-product-product-Pointed-Type A B (x , y))

  preserves-point-map-map-universal-property-smash-Pointed-Type :
    (x : type-Pointed-Type A) →
    map-map-universal-property-smash-Pointed-Type x
      ( point-Pointed-Type B) ＝
    point-Pointed-Type C
  preserves-point-map-map-universal-property-smash-Pointed-Type x =
    ( ap
      ( map-pointed-map f)
      ( inl-glue-smash-Pointed-Type A B x)) ∙
    ( preserves-point-pointed-map f)

  map-universal-property-smash-Pointed-Type :
    type-Pointed-Type A → (B →∗ C)
  pr1 (map-universal-property-smash-Pointed-Type x) =
    map-map-universal-property-smash-Pointed-Type x
  pr2 (map-universal-property-smash-Pointed-Type x) =
    preserves-point-map-map-universal-property-smash-Pointed-Type x

  htpy-preserves-point-map-universal-property-smash-Pointed-Type :
    map-map-universal-property-smash-Pointed-Type
      ( point-Pointed-Type A) ~
    map-constant-pointed-map B C
  htpy-preserves-point-map-universal-property-smash-Pointed-Type y =
    ( ap (map-pointed-map f) (inr-glue-smash-Pointed-Type A B y)) ∙
    ( preserves-point-pointed-map f)

  coherence-point-preserves-point-map-universal-property-smash-Pointed-Type :
    coherence-point-unpointed-htpy-pointed-Π
      ( map-universal-property-smash-Pointed-Type
        ( point-Pointed-Type A))
      ( constant-pointed-map B C)
      ( htpy-preserves-point-map-universal-property-smash-Pointed-Type)
  coherence-point-preserves-point-map-universal-property-smash-Pointed-Type =
    ( right-whisker-concat
      ( ap²
        ( map-pointed-map f)
        ( coh-glue-smash-Pointed-Type A B))
      ( preserves-point-pointed-map f)) ∙
    ( inv right-unit)

  pointed-htpy-preserves-point-map-universal-property-smash-Pointed-Type :
    map-universal-property-smash-Pointed-Type (point-Pointed-Type A) ~∗
    constant-pointed-map B C
  pr1
    pointed-htpy-preserves-point-map-universal-property-smash-Pointed-Type =
    htpy-preserves-point-map-universal-property-smash-Pointed-Type
  pr2
    pointed-htpy-preserves-point-map-universal-property-smash-Pointed-Type =
    coherence-point-preserves-point-map-universal-property-smash-Pointed-Type

  preserves-point-map-universal-property-smash-Pointed-Type :
    map-universal-property-smash-Pointed-Type (point-Pointed-Type A) ＝
    constant-pointed-map B C
  preserves-point-map-universal-property-smash-Pointed-Type =
    eq-pointed-htpy
      ( map-universal-property-smash-Pointed-Type
        ( point-Pointed-Type A))
      ( constant-pointed-map B C)
      ( pointed-htpy-preserves-point-map-universal-property-smash-Pointed-Type)

  pointed-map-universal-property-smash-Pointed-Type :
    A →∗ (pointed-map-Pointed-Type B C)
  pr1 pointed-map-universal-property-smash-Pointed-Type =
    map-universal-property-smash-Pointed-Type
  pr2 pointed-map-universal-property-smash-Pointed-Type =
    preserves-point-map-universal-property-smash-Pointed-Type
```

### The smash product is a pushout of half-smash products

Given two pointed types `X` and `Y`, then the smash product `X ∧∗ Y` is the
pushout

```text
  X ×∗ Y -----> X ⋊∗ Y
    |             |
    |             |
    ∨          ⌜  ∨
  X ⋉∗ Y -----> X ∧∗ Y.
```

Where `X ⋉∗ Y` is the
[left half-smash product](synthetic-homotopy-theory.left-half-smash-products.md),
and `X ⋊∗ Y` is the right half-smash product.

This is Remark 3.4 in {{#cite Lavenir23}}.

**Proof.** Consider the diagram

```text
    X <-------- * --------> Y
    |           |           |
    |           |           |
    ∨           ∨           ∨
  X ×∗ Y <--- X ×∗ Y ---> X ×∗ Y
    |           |           |
    |           |           |
    ∨           ∨           ∨
  X ⋉∗ Y <--- X ×∗ Y ---> X ⋊∗ Y
```

Observe that every column is a cofiber sequence. Therefore, by the 3×3-property
for pushouts, if we take the pushouts of the rows we must also obtain a cofiber
sequence, and the cofibers of the first two rows yield

```text
              X ∨∗ Y
                |
                |
                ∨
              X ×∗ Y
```

of which the smash product `X ∧∗ Y` is the cofiber by definition.

> This remains to be formalized, and depends on another unformalized result, the
> 3×3-property for pushouts.
> [#1326](https://github.com/UniMath/agda-unimath/issues/1326)

As a corollary of the above, the smash product `X ∧∗ Y` is also the cofiber of
the canonical maps `X → X ⋊∗ Y` and `Y → X ⋉∗ Y`, i.e., we have pushout squares

```text
  X ------> X ⋊∗ Y         Y ------> X ⋉∗ Y
  |           |            |           |
  |           |            |           |
  ∨         ⌜ ∨            ∨         ⌜ ∨
  * ------> X ∧∗ Y         * ------> X ∧∗ Y.
```

> This remains to be formalized.

## References

{{#bibliography}}

## See also

- [Wedges of pointed types](synthetic-homotopy-theory.wedges-of-pointed-types.md)
