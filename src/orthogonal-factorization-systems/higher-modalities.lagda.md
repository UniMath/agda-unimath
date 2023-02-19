# Higher modalities

```agda
module orthogonal-factorization-systems.higher-modalities where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.propositions
open import foundation.small-types
open import foundation.subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
```

## Idea

## Definition

```agda
module _
  {l1 l2 : Level}
  ((○ , is-locally-small-○) : locally-small-modal-operator l1 l2 l1)
  (unit-○ : modal-unit ○)
  where

  modality-induction-principle : UU (lsuc l1 ⊔ l2)
  modality-induction-principle =
    (X : UU l1) (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) →
    (x' : ○ X) → ○ (P x')

  modality-computation-principle :
    modality-induction-principle → UU (lsuc l1 ⊔ l2)
  modality-computation-principle ind-○ =
    (X : UU l1) (P : ○ X → UU l1) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ X P f (unit-○ x) ＝ f x

  is-modal-identity-types : UU (lsuc l1 ⊔ l2)
  is-modal-identity-types =
    (X : UU l1) (x y : ○ X) →
    is-modal (unit-○) (type-is-small (is-locally-small-○ X x y))

  is-higher-modality : UU (lsuc l1 ⊔ l2)
  is-higher-modality =
    is-modal-identity-types ×
      Σ ( modality-induction-principle)
        ( modality-computation-principle)

  is-modal-identity-types-is-higher-modality :
    is-higher-modality → is-modal-identity-types
  is-modal-identity-types-is-higher-modality = pr1

  induction-principle-is-higher-modality :
    is-higher-modality → modality-induction-principle
  induction-principle-is-higher-modality = pr1 ∘ pr2

  computation-principle-is-higher-modality :
    (h : is-higher-modality) →
    modality-computation-principle (induction-principle-is-higher-modality h)
  computation-principle-is-higher-modality = pr2 ∘ pr2

higher-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
higher-modality l1 l2 =
  Σ ( locally-small-modal-operator l1 l2 l1)
    ( λ ○ →
      Σ ( modal-unit (pr1 ○))
        ( is-higher-modality ○))

module _
  {l1 l2 : Level} (h : higher-modality l1 l2)
    where

  locally-small-modal-operator-higher-modality :
    locally-small-modal-operator l1 l2 l1
  locally-small-modal-operator-higher-modality = pr1 h

  modal-operator-higher-modality : modal-operator l1 l2
  modal-operator-higher-modality =
    modal-operator-locally-small-modal-operator
      locally-small-modal-operator-higher-modality

  modal-unit-higher-modality : modal-unit modal-operator-higher-modality
  modal-unit-higher-modality = pr1 (pr2 h)

  is-higher-modality-higher-modality :
    is-higher-modality
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
  is-higher-modality-higher-modality = pr2 (pr2 h)

  is-modal-identity-types-higher-modality :
    is-modal-identity-types
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
  is-modal-identity-types-higher-modality =
    is-modal-identity-types-is-higher-modality
    locally-small-modal-operator-higher-modality
    modal-unit-higher-modality
    is-higher-modality-higher-modality

  induction-principle-higher-modality :
    modality-induction-principle
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
  induction-principle-higher-modality =
    induction-principle-is-higher-modality
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
      is-higher-modality-higher-modality

  computation-principle-higher-modality :
      modality-computation-principle
        locally-small-modal-operator-higher-modality
        modal-unit-higher-modality
        induction-principle-higher-modality
  computation-principle-higher-modality =
    computation-principle-is-higher-modality
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
      is-higher-modality-higher-modality
```
