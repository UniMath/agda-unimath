# Reflective subuniverses

```agda
module orthogonal-factorization-systems.reflective-subuniverses where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
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
  {l1 l2 : Level} {○ : modal-operator l1 l1} (unit-○ : modal-unit ○)
  (is-modal' : UU l1 → Prop l2)
  where

  is-reflective-subuniverse : UU (lsuc l1 ⊔ l2)
  is-reflective-subuniverse =
    ((X : UU l1) → type-Prop (is-modal' (○ X))) ×
    ((X : UU l1) → type-Prop (is-modal' X) → (Y : UU l1) → is-local-type (unit-○ {Y}) X)

reflective-subuniverse : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
reflective-subuniverse l1 l2 =
  Σ ( modal-operator l1 l1)
    ( λ ○ →
      Σ ( modal-unit ○)
        ( λ unit-○ →
          Σ ( UU l1 → Prop l2)
            ( is-reflective-subuniverse unit-○)))
``` 