# Reflective subuniverses

```agda
module orthogonal-factorization-systems.reflective-subuniverses where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
```

## Idea

## Definition

```agda
module _
  {l1 l2 l3 : Level} {○ : modal-operator (l1 ⊔ l2) l1} (unit-○ : modal-unit ○)
  (is-modal' : UU (l1 ⊔ l2) → Prop l3)
  where

  is-reflective-subuniverse : UU (lsuc l1 ⊔ lsuc l2 ⊔ l3)
  is-reflective-subuniverse =
    ((X : UU (l1 ⊔ l2)) → type-Prop (is-modal' (raise (l1 ⊔ l2) (○ X)))) ×
    ((X : UU (l1 ⊔ l2)) → type-Prop (is-modal' X) → (Y : UU (l1 ⊔ l2)) → is-local-type (unit-○ {Y}) X)

reflective-subuniverse : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
reflective-subuniverse l1 l2 l3 =
  Σ ( modal-operator (l1 ⊔ l2) l1)
    ( λ ○ →
      Σ ( modal-unit ○)
        ( λ unit-○ →
          Σ ( UU (l1 ⊔ l2) → Prop l3)
            ( is-reflective-subuniverse {l1} {l2} {l3} unit-○)))
```
