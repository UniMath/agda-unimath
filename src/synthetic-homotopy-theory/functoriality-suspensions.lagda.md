# Functoriality of suspensions

```agda
module synthetic-homotopy-theory.functoriality-suspensions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

Any map `f : A → B` induces a map
`map-suspension f : suspension A → suspension B` on the
[suspensions](synthetic-homotopy-theory.suspensions-of-types.md) suspensions of
`A` and `B`.

Furthermore, this operation is functorial: it preserves identities and function
composition.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-suspension-structure : suspension-structure A (suspension B)
  map-suspension-structure =
    north-suspension , south-suspension , meridian-suspension ∘ f

  map-suspension : suspension A → suspension B
  map-suspension =
    map-inv-up-suspension A (suspension B) map-suspension-structure

  compute-north-map-suspension :
    map-suspension (north-suspension) ＝ north-suspension
  compute-north-map-suspension =
    up-suspension-north-suspension A (suspension B) map-suspension-structure

  compute-south-map-suspension :
    map-suspension (south-suspension) ＝ south-suspension
  compute-south-map-suspension =
    up-suspension-south-suspension A (suspension B) map-suspension-structure

  compute-meridian-map-suspension :
    (a : A) →
    coherence-square-identifications
      ( compute-north-map-suspension)
      ( ap map-suspension (meridian-suspension a))
      ( meridian-suspension (f a))
      ( compute-south-map-suspension)
  compute-meridian-map-suspension =
    up-suspension-meridian-suspension A
      ( suspension B)
      ( map-suspension-structure)
```

## Properties

### The induced map on suspensions of the identity is the identity again

```agda
module _
  {l : Level} (A : UU l)
  where

  htpy-function-out-of-suspension-id-map-suspension :
    htpy-function-out-of-suspension A (map-suspension id) id
  pr1 htpy-function-out-of-suspension-id-map-suspension =
    compute-north-map-suspension id
  pr1 (pr2 htpy-function-out-of-suspension-id-map-suspension) =
    compute-south-map-suspension id
  pr2 (pr2 htpy-function-out-of-suspension-id-map-suspension) a =
    coherence-square-identifications-right-paste
      ( ap (map-suspension id) (meridian-suspension a))
      ( compute-south-map-suspension id)
      ( compute-north-map-suspension id)
      ( meridian-suspension a)
      ( inv (ap-id (meridian-suspension a)))
      ( compute-meridian-map-suspension id a)

  id-map-suspension : map-suspension (id {A = A}) ~ id
  id-map-suspension =
    htpy-htpy-function-out-of-suspension A
      ( map-suspension id)
      ( id)
      ( htpy-function-out-of-suspension-id-map-suspension)
```

### The induced map on suspensions of a composition is the composition of the induced maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : A → B) (g : B → C)
  where

  preserves-comp-map-suspension-north :
    (map-suspension g ∘ map-suspension f) north-suspension ＝
    map-suspension (g ∘ f) north-suspension
  preserves-comp-map-suspension-north =
    ap (map-suspension g) (compute-north-map-suspension f) ∙
    ( compute-north-map-suspension g ∙
      ( inv (compute-north-map-suspension (g ∘ f))))

  preserves-comp-map-suspension-south :
    (map-suspension g ∘ map-suspension f) south-suspension ＝
    map-suspension (g ∘ f) south-suspension
  preserves-comp-map-suspension-south =
    ap (map-suspension g) (compute-south-map-suspension f) ∙
    ( compute-south-map-suspension g ∙
      ( inv (compute-south-map-suspension (g ∘ f))))

  coherence-square-identifications-comp-map-suspension :
    (a : A) →
    coherence-square-identifications
      ( preserves-comp-map-suspension-north)
      ( ap (map-suspension g ∘ map-suspension f) (meridian-suspension a))
      ( ap (map-suspension (g ∘ f)) (meridian-suspension a))
      ( preserves-comp-map-suspension-south)
  coherence-square-identifications-comp-map-suspension a =
    coherence-square-identifications-comp-horizontal
      ( ap (map-suspension g ∘ map-suspension f) (meridian-suspension a))
      ( ap (map-suspension g) (meridian-suspension (f a)))
      ( ap (map-suspension (g ∘ f)) (meridian-suspension a))
      ( coherence-square-identifications-left-paste
        ( ap (map-suspension g) (ap (map-suspension f) (meridian-suspension a)))
        ( ap (map-suspension g) (compute-south-map-suspension f))
        ( ap (map-suspension g) (compute-north-map-suspension f))
        ( ap (map-suspension g) (meridian-suspension (f a)))
        ( inv
          ( ap-comp
            ( map-suspension g)
            ( map-suspension f)
            ( meridian-suspension a)))
        ( coherence-square-identifications-ap
          ( map-suspension g)
          ( ap (map-suspension f) (meridian-suspension a))
          ( compute-south-map-suspension f)
          ( compute-north-map-suspension f)
          ( meridian-suspension (f a))
          ( compute-meridian-map-suspension f a)))
      ( coherence-square-identifications-comp-horizontal
        ( ap (map-suspension g) (meridian-suspension (f a)))
        ( meridian-suspension (g (f a)))
        ( ap (map-suspension (g ∘ f)) (meridian-suspension a))
        ( compute-meridian-map-suspension g (f a))
        ( coherence-square-identifications-horizontal-inv
          ( ap (map-suspension (g ∘ f)) (meridian-suspension a))
          ( compute-south-map-suspension (g ∘ f))
          ( compute-north-map-suspension (g ∘ f))
          ( meridian-suspension (g (f a)))
          ( compute-meridian-map-suspension (g ∘ f) a)))

  htpy-function-out-of-suspension-comp-map-suspension :
    htpy-function-out-of-suspension A
      ( map-suspension g ∘ map-suspension f)
      ( map-suspension (g ∘ f))
  pr1 htpy-function-out-of-suspension-comp-map-suspension =
    preserves-comp-map-suspension-north
  pr1 (pr2 htpy-function-out-of-suspension-comp-map-suspension) =
    preserves-comp-map-suspension-south
  pr2 (pr2 htpy-function-out-of-suspension-comp-map-suspension) =
    coherence-square-identifications-comp-map-suspension

  preserves-comp-map-suspension' :
    map-suspension g ∘ map-suspension f ~ map-suspension (g ∘ f)
  preserves-comp-map-suspension' =
    htpy-htpy-function-out-of-suspension A
      ( map-suspension g ∘ map-suspension f)
      ( map-suspension (g ∘ f))
      ( htpy-function-out-of-suspension-comp-map-suspension)

  preserves-comp-map-suspension :
    map-suspension (g ∘ f) ~ map-suspension g ∘ map-suspension f
  preserves-comp-map-suspension = inv-htpy preserves-comp-map-suspension'
```
