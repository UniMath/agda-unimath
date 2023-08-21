# Functoriality of higher modalities

```agda
module orthogonal-factorization-systems.functoriality-higher-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.univalence
open import foundation.identity-types
open import foundation.small-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.higher-modalities
open import orthogonal-factorization-systems.induction-modalities
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

  ap-higher-modality : {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  ap-higher-modality = ap-ind-modality unit-○ ind-○
```

### Naturality of the unit

```agda
module _
  {l1 l2 : Level}
  (((○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○) :
      higher-modality l1 l2)
  where

  naturality-unit-higher-modality :
    {X Y : UU l1} (f : X → Y) →
    ((ap-ind-modality unit-○ ind-○ f) ∘ unit-○) ~ (unit-○ ∘ f)
  naturality-unit-higher-modality =
    naturality-unit-modality unit-○ ind-○ compute-ind-○
```

### Functoriality

```agda
module _
  {l : Level}
  (((○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○) :
      higher-modality l l)
  where

  functoriality-higher-modality :
    {X Y Z : UU l}
    (f : X → Y) (g : Y → Z) →
    ( ap-ind-modality unit-○ ind-○ g ∘ ap-ind-modality unit-○ ind-○ f) ~
    ( ap-ind-modality unit-○ ind-○ (g ∘ f))
  functoriality-higher-modality {X} {Y} {Z} f g =
    ind-subuniverse-ind-modality unit-○ ind-○ X _
      ( λ x' →
        -- TODO: we should be able to avoid univalence here
        tr
          ( is-modal unit-○)
          ( eq-equiv _ _ (inv-equiv-is-small (is-locally-small-○ Z _ _)))
          ( Id-○ Z _ _))
      ( λ x →
        ( ( ap
            ( ap-ind-modality unit-○ ind-○ g)
            ( compute-ind-○ X (λ _ → Y) (unit-○ ∘ f) x)) ∙
          ( compute-ind-○ Y (λ _ → Z) (unit-○ ∘ g) (f x))) ∙
        ( inv (compute-ind-○ X (λ _ → Z) (unit-○ ∘ (g ∘ f)) x)))
```

## References

- Felix Cherubini, _DCHoTT-Agda_/Im.agda, file in GitHub repository
  (<https://github.com/felixwellen/DCHoTT-Agda/blob/master/Im.agda>)
