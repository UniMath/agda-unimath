# Induction on modalities

```agda
module orthogonal-factorization-systems.induction-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.univalence
open import foundation.identity-types
open import foundation.small-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

TODO

## Definition

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

  rec-modality : UU (lsuc l1 ⊔ l2)
  rec-modality = (X Y : UU l1) → (X → ○ Y) → ○ X → ○ Y

  compute-ind-modality : ind-modality → UU (lsuc l1 ⊔ l2)
  compute-ind-modality ind-○ =
    (X : UU l1) (P : ○ X → UU l1) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ X P f (unit-○ x) ＝ f x

  dependent-universal-property-modality : UU (lsuc l1 ⊔ l2)
  dependent-universal-property-modality =
    Σ ind-modality compute-ind-modality

  rec-ind-modality : ind-modality → rec-modality
  rec-ind-modality ind X Y = ind X (λ _ → Y)
```

## Properties

### The modal operator's action on maps

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ap-rec-modality : rec-modality unit-○ → {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  ap-rec-modality rec-○ {X} {Y} f = rec-○ X Y (unit-○ ∘ f)

  ap-ind-modality : ind-modality unit-○ → {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  ap-ind-modality ind-○ = ap-rec-modality (rec-ind-modality unit-○ ind-○)
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
    ((ap-ind-modality unit-○ ind-○ f) ∘ unit-○) ~ (unit-○ ∘ f)
  naturality-unit-modality {X} {Y} f =
    compute-ind-○ X (λ _ → Y) (unit-○ ∘ f)
```

## See also

- [Functoriality of higher modalities](orthogonal-factorization-systems.functoriality-higher-modalities.md)
