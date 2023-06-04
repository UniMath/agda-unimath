# The truncation modalities

```agda
module orthogonal-factorization-systems.truncation-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The truncation operation is a higher modality for every truncation level.

## Definition

```agda
trunc-operator-modality :
  (l : Level) (k : 𝕋) → operator-modality l l
trunc-operator-modality _ = type-trunc

trunc-unit-modality :
  {l : Level} {k : 𝕋} → unit-modality (trunc-operator-modality l k)
trunc-unit-modality = unit-trunc
```

## Properties

### The truncation modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-trunc :
  {l : Level} {k : 𝕋} →
  is-uniquely-eliminating-modality (trunc-unit-modality {l} {k})
is-uniquely-eliminating-modality-trunc {k = k} A P =
  dependent-universal-property-trunc
    ( λ z → (type-trunc k (P z) , is-trunc-type-trunc))
```
