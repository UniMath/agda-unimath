# Higher modalities

```agda
module orthogonal-factorization-systems.uniquely-eliminating-modalities where

open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
```

## Idea

## Definition

```agda
module _
  {l : Level} {○ : modal-operator l} (unit-○ : modal-unit ○)
  where

  is-uniquely-eliminating-modality : UU (lsuc l)
  is-uniquely-eliminating-modality =
    (X : UU l) (P : ○ X → UU l) →
    is-local-type (unit-○ {X}) ((○x : ○ X) → ○ (P ○x))
```