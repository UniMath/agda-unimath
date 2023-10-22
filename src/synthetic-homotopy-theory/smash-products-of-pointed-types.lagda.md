# Smash products of pointed types

```agda
module synthetic-homotopy-theory.smash-products-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-spans-of-pointed-types
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
    v        ⌜  v
  unit -----> A ∧∗ B
```

where the map `A ∨∗ B → A ×∗ B` is the canonical inclusion
`map-wedge-prod-Pointed-Type` from the
[wedge](synthetic-homotopy-theory.wedges-of-pointed-types.md) into the
[pointed cartesian product](structured-types.pointed-cartesian-product-types.md).

## Definition

```agda
smash-prod-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
smash-prod-Pointed-Type A B =
  pushout-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))

infixr 15 _∧∗_
_∧∗_ = smash-prod-Pointed-Type
```

**Note**: The symbols used for the smash product `_∧∗_` are the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` `\and`),
and the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input:
`\ast`), not the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
cogap-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  type-cocone-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B)) X →
  (A ∧∗ B) →∗ X
cogap-smash-prod-Pointed-Type {A = A} {B} =
  cogap-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))

map-cogap-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  type-cocone-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))
    ( X) →
  type-Pointed-Type (A ∧∗ B) → type-Pointed-Type X
map-cogap-smash-prod-Pointed-Type c =
  pr1 (cogap-smash-prod-Pointed-Type c)
```

## Properties

### The canonical pointed map from the product to the smash product

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-smash-prod-prod-Pointed-Type : (A ×∗ B) →∗ (A ∧∗ B)
  pointed-map-smash-prod-prod-Pointed-Type =
    inl-pushout-Pointed-Type
      ( pointed-map-prod-wedge-Pointed-Type A B)
      ( terminal-pointed-map (A ∨∗ B))

  map-smash-prod-prod-Pointed-Type :
    type-Pointed-Type (A ×∗ B) → type-Pointed-Type (A ∧∗ B)
  map-smash-prod-prod-Pointed-Type =
    map-pointed-map pointed-map-smash-prod-prod-Pointed-Type
```

### Pointed maps into pointed types `A` and `B` induce a pointed map into `A ∧∗ B`

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {S : Pointed-Type l3}
  where

  gap-smash-prod-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → S →∗ (A ∧∗ B)
  gap-smash-prod-Pointed-Type f g =
    pointed-map-smash-prod-prod-Pointed-Type A B ∘∗
    gap-prod-Pointed-Type f g

  map-gap-smash-prod-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → type-Pointed-Type S → type-Pointed-Type (A ∧∗ B)
  map-gap-smash-prod-Pointed-Type f g =
    pr1 (gap-smash-prod-Pointed-Type f g)
```

### The canonical map from the wedge sum to the smash product identifies all points

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-smash-prod-wedge-Pointed-Type : (A ∨∗ B) →∗ (A ∧∗ B)
  pointed-map-smash-prod-wedge-Pointed-Type =
    pointed-map-smash-prod-prod-Pointed-Type A B ∘∗
    pointed-map-prod-wedge-Pointed-Type A B

  map-smash-prod-wedge-Pointed-Type :
    type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ∧∗ B)
  map-smash-prod-wedge-Pointed-Type =
    map-pointed-map pointed-map-smash-prod-wedge-Pointed-Type

  eq-map-smash-prod-wedge-Pointed-Type :
    ( x : type-Pointed-Type (A ∨∗ B)) →
    map-smash-prod-wedge-Pointed-Type x ＝
    point-Pointed-Type (A ∧∗ B)
  eq-map-smash-prod-wedge-Pointed-Type x =
    ( glue-pushout
      ( map-prod-wedge-Pointed-Type A B)
      ( map-pointed-map {A = A ∨∗ B} {B = unit-Pointed-Type}
        ( terminal-pointed-map (A ∨∗ B)))
      ( x)) ∙
    ( ( htpy-right-whisk
        ( htpy-pointed-htpy
          ( inr-pushout-Pointed-Type
            ( pointed-map-prod-wedge-Pointed-Type A B)
            ( terminal-pointed-map (A ∨∗ B)))
          ( inclusion-point-Pointed-Type (A ∧∗ B))
          ( is-initial-unit-Pointed-Type
            ( A ∧∗ B)
            ( inr-pushout-Pointed-Type
              ( pointed-map-prod-wedge-Pointed-Type A B)
              ( terminal-pointed-map (A ∨∗ B)))))
        ( map-terminal-pointed-map (A ∨∗ B)))
      ( x)) ∙
    ( preserves-point-pointed-map
      ( inclusion-point-Pointed-Type (A ∧∗ B)))

  coh-eq-map-smash-prod-wedge-Pointed-Type :
    ( ap
      ( map-smash-prod-wedge-Pointed-Type)
      ( glue-wedge-Pointed-Type A B)) ∙
    ( eq-map-smash-prod-wedge-Pointed-Type
        ( map-inr-wedge-Pointed-Type A B (point-Pointed-Type B))) ＝
    ( eq-map-smash-prod-wedge-Pointed-Type
      ( map-inl-wedge-Pointed-Type A B (point-Pointed-Type A)))
  coh-eq-map-smash-prod-wedge-Pointed-Type =
    ( inv-map-compute-dependent-identification-eq-value-function
      ( map-smash-prod-wedge-Pointed-Type)
      ( map-pointed-map
        ( constant-pointed-map (A ∨∗ B) (A ∧∗ B)))
      ( glue-wedge-Pointed-Type A B)
      ( eq-map-smash-prod-wedge-Pointed-Type
        ( map-inl-wedge-Pointed-Type A B (point-Pointed-Type A)))
      ( eq-map-smash-prod-wedge-Pointed-Type
        ( map-inr-wedge-Pointed-Type A B (point-Pointed-Type B)))
      ( apd
        ( eq-map-smash-prod-wedge-Pointed-Type)
        ( glue-wedge-Pointed-Type A B))) ∙
    ( identification-left-whisk
      ( eq-map-smash-prod-wedge-Pointed-Type
        ( map-inl-wedge-Pointed-Type A B (point-Pointed-Type A)))
      ( ap-const
        ( point-Pointed-Type (A ∧∗ B))
        ( glue-wedge-Pointed-Type A B))) ∙
    ( right-unit)
```

### The map from the pointed product to the smash product identifies elements

of the form (x, b) and (a, y).

```agda
module _
  {l1 l2 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  glue-smash-prod-Pointed-Type :
    (x : type-Pointed-Type A) (y : type-Pointed-Type B) →
    map-smash-prod-prod-Pointed-Type A B
      ( x , point-Pointed-Type B) ＝
    map-smash-prod-prod-Pointed-Type A B
      ( point-Pointed-Type A , y)
  glue-smash-prod-Pointed-Type x y =
    ( ap
      ( map-smash-prod-prod-Pointed-Type A B)
      ( inv (inl-prod-wedge-Pointed-Type A B x))) ∙
    ( eq-map-smash-prod-wedge-Pointed-Type A B
      ( map-inl-wedge-Pointed-Type A B x) ∙
    ( inv
      ( eq-map-smash-prod-wedge-Pointed-Type A B
        ( map-inr-wedge-Pointed-Type A B y))) ∙
    ( ap
      ( map-smash-prod-prod-Pointed-Type A B)
      ( inr-prod-wedge-Pointed-Type A B y)))

  coh-glue-smash-prod-Pointed-Type :
    ( glue-smash-prod-Pointed-Type
      ( point-Pointed-Type A)
      ( point-Pointed-Type B)) ＝
    ( refl)
  coh-glue-smash-prod-Pointed-Type =
    ( ap
      ( λ p →
        ( ap
          ( map-smash-prod-prod-Pointed-Type A B)
          ( inv (inl-prod-wedge-Pointed-Type A B (point-Pointed-Type A)))) ∙
        ( p ∙
        ( ap
          ( map-smash-prod-prod-Pointed-Type A B)
          ( inr-prod-wedge-Pointed-Type A B (point-Pointed-Type B)))))
      ( inv
        ( right-transpose-eq-concat
          ( ap
            ( map-smash-prod-wedge-Pointed-Type A B)
            ( glue-wedge-Pointed-Type A B))
          ( eq-map-smash-prod-wedge-Pointed-Type A B
            ( map-inr-wedge-Pointed-Type A B (point-Pointed-Type B)))
          ( eq-map-smash-prod-wedge-Pointed-Type A B
            ( map-inl-wedge-Pointed-Type A B (point-Pointed-Type A)))
          ( coh-eq-map-smash-prod-wedge-Pointed-Type A B)))) ∙
    ( ap
      ( λ p →
        ( ap
          ( map-smash-prod-prod-Pointed-Type A B)
          ( inv (inl-prod-wedge-Pointed-Type A B (point-Pointed-Type A)))) ∙
        ( p ∙
        ( ap
          ( map-smash-prod-prod-Pointed-Type A B)
          ( inr-prod-wedge-Pointed-Type A B (point-Pointed-Type B)))))
      ( ap-comp
        ( map-smash-prod-prod-Pointed-Type A B)
        ( map-prod-wedge-Pointed-Type A B)
        ( glue-wedge-Pointed-Type A B))) ∙
    ( identification-left-whisk
      ( ap
        ( map-smash-prod-prod-Pointed-Type A B)
        ( inv (inl-prod-wedge-Pointed-Type A B (point-Pointed-Type A))))
      ( inv
        ( ap-concat
          ( map-smash-prod-prod-Pointed-Type A B)
          ( ap
            ( map-prod-wedge-Pointed-Type A B)
            ( glue-wedge-Pointed-Type A B))
          ( inr-prod-wedge-Pointed-Type A B (point-Pointed-Type B))))) ∙
    ( inv
      ( ap-concat
        ( map-smash-prod-prod-Pointed-Type A B)
        ( inv (inl-prod-wedge-Pointed-Type A B (point-Pointed-Type A)))
        ( ( ap
            ( map-prod-wedge-Pointed-Type A B)
            ( glue-wedge-Pointed-Type A B)) ∙
          ( inr-prod-wedge-Pointed-Type A B (point-Pointed-Type B))))) ∙
    ( ap²
      ( map-smash-prod-prod-Pointed-Type A B)
      ( inv
        ( left-transpose-eq-concat
          ( inl-prod-wedge-Pointed-Type A B (point-Pointed-Type A))
          ( refl)
          ( ( ap
              ( map-prod-wedge-Pointed-Type A B)
              ( glue-wedge-Pointed-Type A B) ∙
            ( inr-prod-wedge-Pointed-Type A B (point-Pointed-Type B))))
          ( inv
            ( compute-glue-cogap
              ( map-pointed-map
                ( inclusion-point-Pointed-Type A))
              ( map-pointed-map
                ( inclusion-point-Pointed-Type B))
              ( cocone-type-cocone-Pointed-Type
                ( inclusion-point-Pointed-Type A)
                ( inclusion-point-Pointed-Type B)
                ( cocone-prod-wedge-Pointed-Type A B))
              ( point-Pointed-Type unit-Pointed-Type))))))
```

### The universal property of the smash product

```agda
{-eval-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) (C : Pointed-Type l3) →
  ((A ∧∗ B) →∗ C) → (A →∗ (pointed-map-Pointed-Type B C))
pr1 (pr1 (eval-smash-prod-Pointed-Type A B C f) x) y =
  map f
    ( map
      ( pointed-map-smash-prod-prod-Pointed-Type A B) (x , y))
pr2 (pr1 (eval-smash-prod-Pointed-Type A B C f) x) =
  ( ap
    ( map f)
    ( glue-smash-prod-Pointed-Type x (point-Pointed-Type B))) ∙
  ( preserves-point-pointed-map f)
pr2 (eval-smash-prod-Pointed-Type A B C f) =
  eq-pair-Σ
    ( eq-htpy
      ( λ y →
        ( ap
          ( map f)
          ( inv
            ( glue-smash-prod-Pointed-Type (point-Pointed-Type A) y))) ∙
        ( preserves-point-pointed-map f)))
    {!!}-}
```

## See also

- [Wedges of pointed types](synthetic-homotopy-theory.wedges-of-pointed-types.md)
