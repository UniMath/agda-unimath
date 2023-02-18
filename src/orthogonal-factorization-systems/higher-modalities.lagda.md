# Higher modalities

```agda
module orthogonal-factorization-systems.higher-modalities where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
```

## Idea

## Definition

```agda
module _
  {l : Level} {○ : modal-operator l} (unit-○ : modal-unit ○)
  where

  modality-induction-principle : UU (lsuc l)
  modality-induction-principle =
    (X : UU l) (P : ○ X → UU l) →
    ((x : X) → ○ (P (unit-○ x))) →
    (○x : ○ X) → ○ (P ○x)
  
  modality-computation-principle : modality-induction-principle → UU (lsuc l)
  modality-computation-principle ind-○ =
    (X : UU l) (P : ○ X → UU l) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ X P f (unit-○ x) ＝ f x

  is-modal-identity-types : UU (lsuc l)
  is-modal-identity-types =
    (X : UU l) (x y : ○ X) → is-modal (unit-○) (x ＝ y)

  is-higher-modality : UU (lsuc l)
  is-higher-modality =
    is-modal-identity-types ×
      Σ modality-induction-principle modality-computation-principle
```
