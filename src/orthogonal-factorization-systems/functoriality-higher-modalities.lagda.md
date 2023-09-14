# Functoriality of higher modalities

```agda
module orthogonal-factorization-systems.functoriality-higher-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.path-algebra
open import foundation.homotopies
open import foundation.identity-types
open import foundation.small-types
open import foundation.transport
open import foundation.univalence
open import foundation.universe-levels

open import orthogonal-factorization-systems.higher-modalities
open import orthogonal-factorization-systems.induction-modalities
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.subuniverse-induction
```

</details>

## Properties

### Action on maps

```agda
module _
  {l1 l2 : Level} (m : higher-modality l1 l2)
  where

  ap-map-higher-modality :
    {X Y : UU l1} →
    (X → Y) → operator-higher-modality m X → operator-higher-modality m Y
  ap-map-higher-modality =
    ap-map-ind-modality (unit-higher-modality m) (ind-higher-modality m)
```

### Functoriality

```agda
module _
  {l : Level} (m : higher-modality l l)
  where

  functoriality-higher-modality :
    {X Y Z : UU l} (g : Y → Z) (f : X → Y) →
    ( ap-map-higher-modality m g ∘ ap-map-higher-modality m f) ~
    ( ap-map-higher-modality m (g ∘ f))
  functoriality-higher-modality {X} {Y} {Z} g f =
    ind-subuniverse-Id-higher-modality m
      ( ap-map-higher-modality m g ∘ ap-map-higher-modality m f)
      ( ap-map-higher-modality m (g ∘ f))
      ( λ x →
        ( ap
          ( ap-map-higher-modality m g)
          ( compute-rec-higher-modality m X Y
            ( unit-higher-modality m ∘ f)
            ( x))) ∙
        ( ( compute-rec-higher-modality m Y Z
            ( unit-higher-modality m ∘ g)
            ( f x)) ∙
          ( inv
            ( compute-rec-higher-modality m X Z
              ( unit-higher-modality m ∘ (g ∘ f))
              ( x)))))
```

### Naturality of the unit of a higher modality

```text
         f
    X ------> Y
    |         |
    |         |
    v         v
   ○ X ----> ○ Y
        ○ f
```

```agda
module _
  {l1 l2 : Level} (m : higher-modality l1 l2)
  where

  naturality-unit-higher-modality :
    {X Y : UU l1} (f : X → Y) →
    ( ap-map-higher-modality m f ∘ unit-higher-modality m) ~
    ( unit-higher-modality m ∘ f)
  naturality-unit-higher-modality =
    naturality-unit-ind-modality
      ( unit-higher-modality m)
      ( ind-higher-modality m)
      ( compute-ind-higher-modality m)
```

```agda
  naturality-unit-higher-modality' :
    {X Y : UU l1} (f : X → Y) {x x' : X} →
    unit-higher-modality m x ＝ unit-higher-modality m x' →
    unit-higher-modality m (f x) ＝ unit-higher-modality m (f x')
  naturality-unit-higher-modality' =
    naturality-unit-ind-modality'
      ( unit-higher-modality m)
      ( ind-higher-modality m)
      ( compute-ind-higher-modality m)

module _
  {l : Level} (m : higher-modality l l)
  where

  compute-naturality-unit-ind-modality :
    {X Y Z : UU l} (g : Y → Z) (f : X → Y) (x : X) →
    ( ( functoriality-higher-modality m g f (unit-higher-modality m x)) ∙
      ( naturality-unit-higher-modality m (g ∘ f) x)) ＝
    ( ( ap
        ( ap-map-higher-modality m g)
        ( naturality-unit-higher-modality m f x)) ∙
      ( naturality-unit-higher-modality m g (f x)))
  compute-naturality-unit-ind-modality {X} {Y} {Z} g f x =
    ( ap
      ( _∙
        compute-rec-higher-modality m X Z (unit-higher-modality m ∘ (g ∘ f)) x)
      ( compute-ind-subuniverse-Id-higher-modality m
        ( ap-map-higher-modality m g ∘ ap-map-higher-modality m f)
        ( ap-map-higher-modality m (g ∘ f))
        ( _)
        ( x))) ∙
    ( assoc
      ( ap
        ( ap-map-higher-modality m g)
        ( compute-rec-higher-modality m X Y (pr1 (pr2 m) ∘ f) x))
      ( ( compute-rec-higher-modality m Y Z (pr1 (pr2 m) ∘ g) (f x)) ∙
        ( inv (compute-rec-higher-modality m X Z (pr1 (pr2 m) ∘ g ∘ f) x)))
      ( compute-rec-higher-modality m X Z (pr1 (pr2 m) ∘ g ∘ f) x)) ∙
    ( ap
      ( ap
        ( ap-map-higher-modality m g)
        ( compute-rec-higher-modality m X Y (pr1 (pr2 m) ∘ f) x) ∙_)
      ( is-section-right-concat-inv
        ( compute-rec-higher-modality m Y Z (pr1 (pr2 m) ∘ g) (f x))
        ( compute-rec-higher-modality m X Z (pr1 (pr2 m) ∘ g ∘ f) x)))
```

## References

- Felix Cherubini, _DCHoTT-Agda_/Im.agda, file in GitHub repository
  (<https://github.com/felixwellen/DCHoTT-Agda/blob/master/Im.agda>)
