# The raise modalities

```agda
open import foundation.function-extensionality-axiom

module
  orthogonal-factorization-systems.raise-modalities
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types funext
open import foundation.raising-universe-levels funext
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators funext
open import orthogonal-factorization-systems.types-local-at-maps funext
open import orthogonal-factorization-systems.uniquely-eliminating-modalities funext
```

</details>

## Idea

The operations of
[raising universe levels](foundation.raising-universe-levels.md) are trivially
[higher modalities](orthogonal-factorization-systems.higher-modalities.md), and
in the case that `l1 ⊔ l2 = l1`, we recover the
[identity modality](orthogonal-factorization-systems.identity-modality.md).

## Definition

```agda
operator-raise-modality :
  (l1 l2 : Level) → operator-modality l1 (l1 ⊔ l2)
operator-raise-modality l1 l2 = raise l2

unit-raise-modality :
  {l1 l2 : Level} → unit-modality (operator-raise-modality l1 l2)
unit-raise-modality = map-raise
```

## Properties

### The raise modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-raise-modality :
  {l1 l2 : Level} →
  is-uniquely-eliminating-modality (unit-raise-modality {l1} {l2})
is-uniquely-eliminating-modality-raise-modality {l1} {l2} P =
  is-local-dependent-type-is-equiv
    ( unit-raise-modality)
    ( is-equiv-map-raise)
    ( operator-raise-modality l1 l2 ∘ P)
```

### In the case that `l1 ⊔ l2 = l1` we recover the identity modality

This remains to be made formal.
[#739](https://github.com/UniMath/agda-unimath/issues/739)
