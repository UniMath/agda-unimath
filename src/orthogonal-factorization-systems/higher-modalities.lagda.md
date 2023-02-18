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
  {(○ , is-locally-small-○) : locally-small-modal-operator l1 l2}
  (unit-○ : modal-unit ○)
  where

  modality-induction-principle : UU (lsuc l1 ⊔ l2)
  modality-induction-principle =
    (X : UU l1) (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) →
    (x' : ○ X) → ○ (P x')

  modality-computation-principle : modality-induction-principle → UU (lsuc l1 ⊔ l2)
  modality-computation-principle ind-○ =
    (X : UU l1) (P : ○ X → UU l1) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ X P f (unit-○ x) ＝ f x

  is-modal-identity-types : UU (lsuc l1 ⊔ l2)
  is-modal-identity-types =
    (X : UU l1) (x y : ○ X) → is-modal (unit-○) (type-is-small (is-locally-small-○ X x y))

  is-higher-modality : UU (lsuc l1 ⊔ l2)
  is-higher-modality =
    is-modal-identity-types ×
      Σ modality-induction-principle modality-computation-principle
```
