# Modal operators

```agda
module orthogonal-factorization-systems.modal-operators where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.small-types
open import foundation.subuniverses
open import foundation.universe-levels
```

</details>

## Idea

Underlying every modality is a **modal operator**, which is an operation on
types that construct new types. For a _monadic_ modality `○`, there is moreover
a **modal unit** that compares every type `X` to its modal type `○ X`
(`X → ○ X`).

## Definitions

### Modal operators

```agda
operator-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
operator-modality l1 l2 = UU l1 → UU l2
```

### Modal units

```agda
unit-modality : {l1 l2 : Level} → operator-modality l1 l2 → UU (lsuc l1 ⊔ l2)
unit-modality {l1} ○ = {X : UU l1} → X → ○ X
```

### The subuniverse of modal types

```agda
module _
  {l1 l2 : Level} {○ : operator-modality l1 l2} (unit-○ : unit-modality ○)
  where

  is-modal : (X : UU l1) → UU (l1 ⊔ l2)
  is-modal X = is-equiv (unit-○ {X})

  is-modal-family : {l3 : Level} {X : UU l3} (P : X → UU l1) → UU (l1 ⊔ l2 ⊔ l3)
  is-modal-family {X = X} P = (x : X) → is-modal (P x)

  modal-type : UU (lsuc l1 ⊔ l2)
  modal-type = Σ (UU l1) (is-modal)

  is-modal-Prop : (X : UU l1) → Prop (l1 ⊔ l2)
  is-modal-Prop X = is-equiv-Prop (unit-○ {X})

  is-property-is-modal : (X : UU l1) → is-prop (is-modal X)
  is-property-is-modal X = is-prop-type-Prop (is-modal-Prop X)

  is-subuniverse-is-modal : is-subuniverse is-modal
  is-subuniverse-is-modal = is-property-is-modal

  modal-type-subuniverse : subuniverse l1 (l1 ⊔ l2)
  modal-type-subuniverse = is-modal-Prop
```

### Modal small types

A small type is said to be modal if its small equivalent is modal.

```agda
is-modal-type-is-small :
  {l1 l2 l3 : Level}
  {○ : operator-modality l1 l2} (unit-○ : unit-modality ○)
  (X : UU l3) (is-small-X : is-small l1 X) → UU (l1 ⊔ l2)
is-modal-type-is-small unit-○ X is-small-X =
  is-modal unit-○ (type-is-small is-small-X)

module _
  {l1 l2 l3 : Level}
  {○ : operator-modality l1 l2} (unit-○ : unit-modality ○)
  (X : UU l3) (is-small-X : is-small l1 X)
  where

  is-equiv-unit-is-modal-type-is-small :
    is-modal-type-is-small unit-○ X is-small-X →
    is-equiv (unit-○ ∘ map-equiv-is-small is-small-X)
  is-equiv-unit-is-modal-type-is-small =
    is-equiv-comp
      ( unit-○)
      ( map-equiv-is-small is-small-X)
      ( is-equiv-map-equiv (equiv-is-small is-small-X))

  equiv-unit-is-modal-type-is-small :
    is-modal-type-is-small unit-○ X is-small-X →
    X ≃ ○ (type-is-small is-small-X)
  pr1 (equiv-unit-is-modal-type-is-small m) =
    unit-○ ∘ map-equiv-is-small is-small-X
  pr2 (equiv-unit-is-modal-type-is-small m) =
    is-equiv-unit-is-modal-type-is-small m

  map-inv-unit-is-modal-type-is-small :
    is-modal-type-is-small unit-○ X is-small-X →
    ○ (type-is-small is-small-X) → X
  map-inv-unit-is-modal-type-is-small =
    map-inv-equiv ∘ equiv-unit-is-modal-type-is-small

module _
  {l1 l2 : Level} (l3 : Level)
  {○ : operator-modality l1 l2} (unit-○ : unit-modality ○)
  (X : Small-Type l1 l3)
  where

  is-modal-Small-Type : UU (l1 ⊔ l2)
  is-modal-Small-Type =
    is-modal-type-is-small unit-○
      ( type-Small-Type X)
      ( is-small-type-Small-Type X)

  is-equiv-unit-is-modal-Small-Type :
    is-modal-Small-Type →
    is-equiv (unit-○ ∘ map-equiv (equiv-is-small-type-Small-Type X))
  is-equiv-unit-is-modal-Small-Type =
    is-equiv-unit-is-modal-type-is-small unit-○
      ( type-Small-Type X)
      ( is-small-type-Small-Type X)

  equiv-unit-is-modal-Small-Type :
    is-modal-Small-Type → type-Small-Type X ≃ ○ (small-type-Small-Type X)
  equiv-unit-is-modal-Small-Type =
    equiv-unit-is-modal-type-is-small unit-○
      ( type-Small-Type X)
      ( is-small-type-Small-Type X)

  map-inv-unit-is-modal-Small-Type :
    is-modal-Small-Type → ○ (small-type-Small-Type X) → type-Small-Type X
  map-inv-unit-is-modal-Small-Type =
    map-inv-equiv ∘ equiv-unit-is-modal-Small-Type
```

## References

{{#bibliography}} {{#reference RSS20}}
