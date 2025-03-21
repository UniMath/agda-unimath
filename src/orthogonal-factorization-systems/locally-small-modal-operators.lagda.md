# Locally small modal-operators

```agda
module orthogonal-factorization-systems.locally-small-modal-operators where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.locally-small-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

A [modal operator](orthogonal-factorization-systems.modal-operators.md) is
**locally small** if it maps [small types](foundation.small-types.md) to
[locally small types](foundation.locally-small-types.md).

## Definitions

### Locally small modal operators

```agda
is-locally-small-operator-modality :
  {l1 l2 : Level} (l3 : Level) (○ : operator-modality l1 l2) →
  UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
is-locally-small-operator-modality {l1} l3 ○ =
  (X : UU l1) → is-locally-small l3 (○ X)

locally-small-operator-modality :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
locally-small-operator-modality l1 l2 l3 =
  Σ ( operator-modality l1 l2)
    ( is-locally-small-operator-modality l3)

operator-modality-locally-small-operator-modality :
  {l1 l2 l3 : Level} →
  locally-small-operator-modality l1 l2 l3 → operator-modality l1 l2
operator-modality-locally-small-operator-modality = pr1

is-locally-small-locally-small-operator-modality :
  {l1 l2 l3 : Level} (○ : locally-small-operator-modality l1 l2 l3) →
  is-locally-small-operator-modality l3
    ( operator-modality-locally-small-operator-modality ○)
is-locally-small-locally-small-operator-modality = pr2
```
