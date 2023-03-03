# Uniquely eliminating modalities

```agda
module orthogonal-factorization-systems.uniquely-eliminating-modalities where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
```

## Idea

## Definition

```agda
is-uniquely-eliminating-modality :
  {l1 l2 : Level} {○ : modal-operator l1 l2} → modal-unit ○ → UU (lsuc l1 ⊔ l2)
is-uniquely-eliminating-modality {l1} {l2} {○} unit-○ =
  (X : UU l1) (P : ○ X → UU l1) → is-local-family (unit-○) (○ ∘ P)

uniquely-eliminating-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
uniquely-eliminating-modality l1 l2 =
  Σ ( modal-operator l1 l2)
    ( λ ○ →
      Σ ( modal-unit ○)
        ( is-uniquely-eliminating-modality))
```

### Projections for uniquely eliminating modalities

```agda
module _
  {l1 l2 : Level} {○ : modal-operator l1 l2} {unit-○ : modal-unit ○}
  (is-uem-○ : is-uniquely-eliminating-modality unit-○)
  where

  modal-ind-is-uniquely-eliminating-modality :
    (X : UU l1) (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) → (x' : ○ X) → ○ (P x')
  modal-ind-is-uniquely-eliminating-modality X P =
    map-inv-is-equiv (is-uem-○ X P)

  modal-comp-is-uniquely-eliminating-modality :
    (X : UU l1) (P : ○ X → UU l1) (f : (x : X) → ○ (P (unit-○ x))) →
    (pr1 (pr1 (is-uem-○ X P)) f ∘ unit-○) ~ f
  modal-comp-is-uniquely-eliminating-modality X P =
    htpy-eq ∘ pr2 (pr1 (is-uem-○ X P))

module _
  {l1 l2 : Level}
  ((○ , unit-○ , is-uem-○) : uniquely-eliminating-modality l1 l2)
  where

  modal-operator-uniquely-eliminating-modality : modal-operator l1 l2
  modal-operator-uniquely-eliminating-modality = ○

  modal-unit-uniquely-eliminating-modality : modal-unit ○
  modal-unit-uniquely-eliminating-modality = unit-○

  is-uniquely-eliminating-modality-uniquely-eliminating-modality :
    is-uniquely-eliminating-modality unit-○
  is-uniquely-eliminating-modality-uniquely-eliminating-modality = is-uem-○
```

## Properties

### Types of the form `○ X` are modal

```agda
module _
  {l : Level}
  ((○ , unit-○ , is-uem-○) : uniquely-eliminating-modality l l)
  where

  map-inv-modal-unit-uniquely-eliminating-modality : (X : UU l) → ○ (○ X) → ○ X
  map-inv-modal-unit-uniquely-eliminating-modality X =
    modal-ind-is-uniquely-eliminating-modality is-uem-○ (○ X) (λ _ → X) id
```
