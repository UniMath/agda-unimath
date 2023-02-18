# Modal operators

```agda
module orthogonal-factorization-systems.modal-operators where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.subuniverses
open import foundation.universe-levels
```

## Idea

## Definition

```agda
modal-operator : (l : Level) → UU (lsuc l)
modal-operator l = UU l → UU l

modal-unit : {l : Level} → modal-operator l → UU (lsuc l)
modal-unit {l} ○ = {X : UU l} → X → ○ X
```

## The subuniverse of modal types

```agda
module _
  {l : Level} {○ : modal-operator l} (unit-○ : modal-unit ○)
  where

  is-modal : (X : UU l) → UU l
  is-modal X = is-equiv (unit-○ {X})

  modal-types : UU (lsuc l)
  modal-types = Σ (UU l) is-modal

  is-property-is-modal : (X : UU l) → is-prop (is-modal X)
  is-property-is-modal X = is-property-is-equiv (unit-○ {X})

  is-modal-Prop : (X : UU l) → Prop l
  pr1 (is-modal-Prop X) = is-modal X
  pr2 (is-modal-Prop X) = is-property-is-modal X

  is-subuniverse-is-modal : is-subuniverse is-modal
  is-subuniverse-is-modal = is-property-is-modal

  modal-types-subuniverse : subuniverse l l
  modal-types-subuniverse = is-modal-Prop
```
