# The identity modality

```agda
module orthogonal-factorization-systems.identity-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.function-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The identity operation on types is trivially a
[higher modality](orthogonal-factorization-systems.higher-modalities.md).

## Definition

```agda
operator-id-modality :
  (l : Level) → operator-modality l l
operator-id-modality l = id

unit-id-modality :
  {l : Level} → unit-modality (operator-id-modality l)
unit-id-modality = id
```

## Properties

### The identity modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-id-modality :
  {l : Level} → is-uniquely-eliminating-modality (unit-id-modality {l})
is-uniquely-eliminating-modality-id-modality {l} _ P =
  is-local-family-is-equiv
    ( unit-id-modality)
    ( is-equiv-id)
    ( operator-id-modality l ∘ P)
```
