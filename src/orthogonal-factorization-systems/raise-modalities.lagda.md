# The raise modalities

```agda
module orthogonal-factorization-systems.raise-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.functions
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The operations of
[raising universe levels](foundation.raising-universe-levels.md) are trivially
[higher modalities](orthogonal-factorization-systems.higher-modalities.md), and
in the case that `l1 ⊔ l2 = l1`, we recover the
[trivial modality](orthogonal-factorization-systems.trivial-modality.md).

## Definition

```agda
raise-operator-modality :
  (l1 l2 : Level) → operator-modality l1 (l1 ⊔ l2)
raise-operator-modality l1 l2 = raise l2

raise-unit-modality :
  {l1 l2 : Level} → unit-modality (raise-operator-modality l1 l2)
raise-unit-modality = map-raise
```

## Properties

### The raise modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-raise :
  {l1 l2 : Level} →
  is-uniquely-eliminating-modality (raise-unit-modality {l1} {l2})
is-uniquely-eliminating-modality-raise {l1} {l2} _ P =
  is-local-family-is-equiv
    ( raise-unit-modality)
    ( is-equiv-map-raise)
    ( raise-operator-modality l1 l2 ∘ P)
```

### In the case that `l1 ⊔ l2 = l1` we recover the trivial modality

This remains to be made formal.
