# Modal operators

```agda
module orthogonal-factorization-systems.modal-operators where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.subuniverses
open import foundation.locally-small-types
open import foundation.universe-levels
```

## Idea

## Definition

```agda
modal-operator : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
modal-operator l1 l2 = UU l1 → UU l2

modal-unit : {l1 l2 : Level} → modal-operator l1 l2 → UU (lsuc l1 ⊔ l2)
modal-unit {l1} ○ = {X : UU l1} → X → ○ X
```

## The subuniverse of modal types

```agda
module _
  {l1 l2 : Level} {○ : modal-operator l1 l2} (unit-○ : modal-unit ○)
  where

  is-modal : (X : UU l1) → UU (l1 ⊔ l2)
  is-modal X = is-equiv (unit-○ {X})

  modal-types : UU (lsuc l1 ⊔ l2)
  modal-types = Σ (UU l1) (is-modal)

  is-property-is-modal : (X : UU l1) → is-prop (is-modal X)
  is-property-is-modal X = is-property-is-equiv (unit-○ {X})

  is-modal-Prop : (X : UU l1) → Prop (l1 ⊔ l2)
  pr1 (is-modal-Prop X) = is-modal X
  pr2 (is-modal-Prop X) = is-property-is-modal X

  is-subuniverse-is-modal : is-subuniverse is-modal
  is-subuniverse-is-modal = is-property-is-modal

  modal-types-subuniverse : subuniverse l1 (l1 ⊔ l2)
  modal-types-subuniverse = is-modal-Prop
```

## Locally small modal operators

We say a modal operator is _locally small_ if it maps small types to
locally small types.

```agda
is-locally-small-modal-operator :
  {l1 l2 : Level} (○ : modal-operator l1 l2) → UU (lsuc l1 ⊔ l2)
is-locally-small-modal-operator {l1} ○ = (X : UU l1) → is-locally-small l1 (○ X)

locally-small-modal-operator : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
locally-small-modal-operator l1 l2 =
  Σ (modal-operator l1 l2) (is-locally-small-modal-operator)

modal-operator-locally-small-modal-operator :
  {l1 l2 : Level} → locally-small-modal-operator l1 l2 → modal-operator l1 l2
modal-operator-locally-small-modal-operator = pr1

is-locally-small-modal-operator-locally-small-modal-operator :
  {l1 l2 : Level} (○ : locally-small-modal-operator l1 l2) →
  is-locally-small-modal-operator (modal-operator-locally-small-modal-operator ○)
is-locally-small-modal-operator-locally-small-modal-operator = pr2
```
