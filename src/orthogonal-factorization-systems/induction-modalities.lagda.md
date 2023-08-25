# Induction on modalities

```agda
module orthogonal-factorization-systems.induction-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

TODO

## Definition

### Modal induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ind-modality : UU (lsuc l1 ⊔ l2)
  ind-modality =
    (X : UU l1) (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) →
    (x' : ○ X) → ○ (P x')

  compute-ind-modality : ind-modality → UU (lsuc l1 ⊔ l2)
  compute-ind-modality ind-○ =
    (X : UU l1) (P : ○ X → UU l1) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ X P f (unit-○ x) ＝ f x

  dependent-universal-property-modality : UU (lsuc l1 ⊔ l2)
  dependent-universal-property-modality =
    Σ ind-modality compute-ind-modality
```

### Modal recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-modality : UU (lsuc l1 ⊔ l2)
  rec-modality = (X Y : UU l1) → (X → ○ Y) → ○ X → ○ Y

  compute-rec-modality : rec-modality → UU (lsuc l1 ⊔ l2)
  compute-rec-modality rec-○ =
    (X : UU l1) (Y : UU l1) →
    (f : X → ○ Y) →
    (x : X) → rec-○ X Y f (unit-○ x) ＝ f x

  universal-property-modality : UU (lsuc l1 ⊔ l2)
  universal-property-modality = Σ rec-modality compute-rec-modality
```

## Properties

### Modal recursion from induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-ind-modality : ind-modality unit-○ → rec-modality unit-○
  rec-ind-modality ind X Y = ind X (λ _ → Y)

  compute-rec-compute-ind-modality :
    (ind-○ : ind-modality unit-○) →
    compute-ind-modality unit-○ ind-○ →
    compute-rec-modality unit-○ (rec-ind-modality ind-○)
  compute-rec-compute-ind-modality ind-○ compute-ind-○ X Y =
    compute-ind-○ X (λ _ → Y)
```

### Modal induction gives an inverse to the unit

```agda
is-section-ind-modality :
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  (compute-ind-○ : compute-ind-modality unit-○ ind-○)
  {X : UU l1} {P : ○ X → UU l1} → (precomp-Π unit-○ (○ ∘ P) ∘ ind-○ X P) ~ id
is-section-ind-modality unit-○ ind-○ compute-ind-○ {X} {P} =
  eq-htpy ∘ compute-ind-○ X P

is-retraction-ind-id-modality :
  {l : Level}
  {○ : operator-modality l l}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  (compute-ind-○ : compute-ind-modality unit-○ ind-○)
  {X : UU l} → (ind-○ (○ X) (λ _ → X) id ∘ unit-○) ~ id
is-retraction-ind-id-modality {○ = ○} unit-○ ind-○ compute-ind-○ {X} =
  compute-ind-○ (○ X) (λ _ → X) id

--TODO: do the same for recursion
```

### `dependent-universal-property-modality ≃ section precomp-Π unit-○ (○ ∘ P)`

```agda
-- TODO
  -- equiv-section-dependent-universal-property-modality :
  --   ( {X : UU l1} {P : ○ X → UU l1} → section (precomp-Π unit-○ (○ ∘ P))) ≃
  --   ( dependent-universal-property-modality unit-○)
  -- equiv-section-dependent-universal-property-modality = {!   !}
```

### The modal operator's action on maps

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  map-rec-modality : rec-modality unit-○ → {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  map-rec-modality rec-○ {X} {Y} f = rec-○ X Y (unit-○ ∘ f)

  map-ind-modality : ind-modality unit-○ → {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  map-ind-modality ind-○ = map-rec-modality (rec-ind-modality unit-○ ind-○)
```

### Naturality of the unit

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  (compute-ind-○ : compute-ind-modality unit-○ ind-○)
  where

  naturality-unit-modality :
    {X Y : UU l1} (f : X → Y) →
    (map-ind-modality unit-○ ind-○ f ∘ unit-○) ~ (unit-○ ∘ f)
  naturality-unit-modality {X} {Y} f =
    compute-ind-○ X (λ _ → Y) (unit-○ ∘ f)

  naturality-unit-modality' :
    {X Y : UU l1} (f : X → Y) {x x' : X} →
    unit-○ x ＝ unit-○ x' → unit-○ (f x) ＝ unit-○ (f x')
  naturality-unit-modality' f {x} {x'} p =
    ( inv (naturality-unit-modality f x)) ∙
    ( ( ap (map-ind-modality unit-○ ind-○ f) p) ∙
      ( naturality-unit-modality f x'))
```

## See also

- [Functoriality of higher modalities](orthogonal-factorization-systems.functoriality-higher-modalities.md)
