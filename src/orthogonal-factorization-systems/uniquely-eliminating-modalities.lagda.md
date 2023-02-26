# Uniquely eliminating modalities

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
  {l1 l2 : Level} {○ : modal-operator l1 l2} (unit-○ : modal-unit ○)
  where

  is-uniquely-eliminating-modality : UU (lsuc l1 ⊔ l2)
  is-uniquely-eliminating-modality =
    (X : UU l1) (P : ○ X → UU l1) → is-local-family (unit-○) (○ ∘ P)
```
