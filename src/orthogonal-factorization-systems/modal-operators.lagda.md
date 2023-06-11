# Modal operators

```agda
module orthogonal-factorization-systems.modal-operators where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.locally-small-types
open import foundation.propositions
open import foundation.sigma-closed-subuniverses
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

### Modal operators and units

```agda
operator-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
operator-modality l1 l2 = UU l1 → UU l2

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

  modal-type : UU (lsuc l1 ⊔ l2)
  modal-type = Σ (UU l1) (is-modal)

  is-property-is-modal : (X : UU l1) → is-prop (is-modal X)
  is-property-is-modal X = is-property-is-equiv (unit-○ {X})

  is-modal-Prop : (X : UU l1) → Prop (l1 ⊔ l2)
  pr1 (is-modal-Prop X) = is-modal X
  pr2 (is-modal-Prop X) = is-property-is-modal X

  is-subuniverse-is-modal : is-subuniverse is-modal
  is-subuniverse-is-modal = is-property-is-modal

  modality-subuniverse : subuniverse l1 (l1 ⊔ l2)
  modality-subuniverse = is-modal-Prop
```

### Modal small types

A small type is said to be modal if its small equivalent is modal.

```agda
module _
  {l1 l2 l3 : Level} {○ : operator-modality l1 l2} (unit-○ : unit-modality ○)
  (X : UU l3) (is-small-X : is-small l1 X)
  where

  is-modal-is-small : UU (l1 ⊔ l2)
  is-modal-is-small = is-modal unit-○ (type-is-small is-small-X)

  is-equiv-unit-is-modal-is-small :
    is-modal-is-small →
    is-equiv (unit-○ ∘ map-equiv-is-small is-small-X)
  is-equiv-unit-is-modal-is-small =
    is-equiv-comp _ _ (is-equiv-map-equiv (equiv-is-small is-small-X))

  equiv-unit-is-modal-is-small :
    is-modal-is-small → X ≃ ○ (type-is-small is-small-X)
  pr1 (equiv-unit-is-modal-is-small m) = unit-○ ∘ map-equiv-is-small is-small-X
  pr2 (equiv-unit-is-modal-is-small m) = is-equiv-unit-is-modal-is-small m

  map-inv-unit-is-modal-is-small :
    is-modal-is-small → ○ (type-is-small is-small-X) → X
  map-inv-unit-is-modal-is-small =
    map-inv-equiv ∘ equiv-unit-is-modal-is-small

module _
  {l1 l2 l3 : Level} {○ : operator-modality l1 l2} (unit-○ : unit-modality ○)
  (X : Small-Type l1 l3)
  where

  is-modal-small-type : UU (l1 ⊔ l2)
  is-modal-small-type =
    is-modal-is-small unit-○ (type-Small-Type X) (is-small-type-Small-Type X)

  is-equiv-unit-is-modal-small-type :
    is-modal-small-type →
    is-equiv (unit-○ ∘ map-equiv (equiv-is-small-type-Small-Type X))
  is-equiv-unit-is-modal-small-type =
    is-equiv-unit-is-modal-is-small unit-○
      ( type-Small-Type X)
      ( is-small-type-Small-Type X)

  equiv-unit-is-modal-small-type :
    is-modal-small-type → type-Small-Type X ≃ ○ (small-type-Small-Type X)
  equiv-unit-is-modal-small-type =
    equiv-unit-is-modal-is-small unit-○
      ( type-Small-Type X)
      ( is-small-type-Small-Type X)

  map-inv-unit-is-modal-small-type :
    is-modal-small-type → ○ (small-type-Small-Type X) → type-Small-Type X
  map-inv-unit-is-modal-small-type =
    map-inv-equiv ∘ equiv-unit-is-modal-small-type
```

### Locally small modal operators

We say a modal operator is **locally small** if it maps small types to locally
small types.

```agda
is-locally-small-operator-modality :
  {l1 l2 l3 : Level} (○ : operator-modality l1 l2) → UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
is-locally-small-operator-modality {l1} {l2} {l3} ○ =
  (X : UU l1) → is-locally-small l3 (○ X)

locally-small-operator-modality :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
locally-small-operator-modality l1 l2 l3 =
  Σ ( operator-modality l1 l2)
    ( is-locally-small-operator-modality {l1} {l2} {l3})

operator-modality-locally-small-operator-modality :
  {l1 l2 l3 : Level} →
  locally-small-operator-modality l1 l2 l3 → operator-modality l1 l2
operator-modality-locally-small-operator-modality = pr1

is-locally-small-locally-small-operator-modality :
  {l1 l2 l3 : Level} (○ : locally-small-operator-modality l1 l2 l3) →
  is-locally-small-operator-modality
    ( operator-modality-locally-small-operator-modality ○)
is-locally-small-locally-small-operator-modality = pr2
```

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
