# Modal operators

```agda
module orthogonal-factorization-systems.modal-operators where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.propositions
open import foundation.subuniverses
open import foundation.universe-levels
```

## Idea

## Definition

```agda
modal-operator : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
modal-operator l1 l2 = UU (l1 ⊔ l2) → UU l2

modal-unit : {l1 l2 : Level} → modal-operator l1 l2 → UU (lsuc l1 ⊔ lsuc l2)
modal-unit {l1} {l2} ○ = (X : UU (l1 ⊔ l2)) → X → ○ X
```

## The subuniverse of modal types

```agda
module _
  {l1 l2 : Level} {○ : modal-operator l1 l2} (unit-○ : modal-unit {l1} {l2} ○)
  where

  is-modal : (X : UU (l1 ⊔ l2)) → UU (l1 ⊔ l2)
  is-modal X = is-equiv (unit-○ X)

  modal-types : UU (lsuc l1 ⊔ lsuc l2)
  modal-types = Σ (UU (l1 ⊔ l2)) is-modal

  is-property-is-modal : (X : UU (l1 ⊔ l2)) → is-prop (is-modal X)
  is-property-is-modal = is-property-is-equiv ∘ unit-○

  is-modal-Prop : (X : UU (l1 ⊔ l2)) → Prop (l1 ⊔ l2)
  pr1 (is-modal-Prop X) = is-modal X
  pr2 (is-modal-Prop X) = is-property-is-modal X

  is-subuniverse-is-modal : is-subuniverse is-modal
  is-subuniverse-is-modal = is-property-is-modal

  modal-types-subuniverse : subuniverse (l1 ⊔ l2) (l1 ⊔ l2)
  modal-types-subuniverse = is-modal-Prop
```
