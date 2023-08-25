# Functoriality of higher modalities

```agda
module orthogonal-factorization-systems.functoriality-higher-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.small-types
open import foundation.transport
open import foundation.univalence
open import foundation.universe-levels

open import orthogonal-factorization-systems.higher-modalities
open import orthogonal-factorization-systems.induction-modalities
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.subuniverse-induction-modalities
```

</details>

## Properties

### Action on maps

```agda
module _
  {l1 l2 : Level}
  (((○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○) :
      higher-modality l1 l2)
  where

  map-higher-modality : {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  map-higher-modality = map-ind-modality unit-○ ind-○
```

### Functoriality

```agda
module _
  {l : Level} (m : higher-modality l l)
  where

  functoriality-higher-modality :
    {X Y Z : UU l}
    (g : Y → Z) (f : X → Y) →
    ( map-higher-modality m g ∘ map-higher-modality m f) ~
    ( map-higher-modality m (g ∘ f))
  functoriality-higher-modality {X} {Y} {Z} g f =
    ind-subuniverse-higher-modality m X _
      ( λ _ → is-modal-Id-higher-modality m)
      ( λ x →
        ( ap
          ( map-higher-modality m g)
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

### Naturality of the unit

```agda
module _
  {l1 l2 : Level} (m : higher-modality l1 l2)
  where

  naturality-unit-higher-modality :
    {X Y : UU l1} (f : X → Y) →
    ( map-higher-modality m f ∘ unit-higher-modality m) ~
    ( unit-higher-modality m ∘ f)
  naturality-unit-higher-modality =
    naturality-unit-modality
      ( unit-higher-modality m)
      ( ind-higher-modality m)
      ( compute-ind-higher-modality m)

  naturality-unit-higher-modality' :
    {X Y : UU l1} (f : X → Y) {x x' : X} →
    unit-higher-modality m x ＝ unit-higher-modality m x' →
    unit-higher-modality m (f x) ＝ unit-higher-modality m (f x')
  naturality-unit-higher-modality' =
    naturality-unit-modality'
      ( unit-higher-modality m)
      ( ind-higher-modality m)
      ( compute-ind-higher-modality m)

module _
  {l : Level} (m : higher-modality l l)
  where

  compute-naturality-unit-modality :
    {X Y Z : UU l}
    (g : Y → Z) (f : X → Y) (x : X) →
    ( ( functoriality-higher-modality m g f (unit-higher-modality m x)) ∙
      ( naturality-unit-higher-modality m (g ∘ f) x)) ＝
    ( ( ap (map-higher-modality m g) (naturality-unit-higher-modality m f x)) ∙
      ( naturality-unit-higher-modality m g (f x)))
  compute-naturality-unit-modality {X} {Y} {Z} g f x =
    ( ap
      ( _∙
        compute-rec-higher-modality m X Z (unit-higher-modality m ∘ (g ∘ f)) x)
      ( compute-ind-subuniverse-higher-modality m
        X _ ( λ _ → is-modal-Id-higher-modality m) _ x)) ∙
    {!   !}
```

## References

- Felix Cherubini, _DCHoTT-Agda_/Im.agda, file in GitHub repository
  (<https://github.com/felixwellen/DCHoTT-Agda/blob/master/Im.agda>)
