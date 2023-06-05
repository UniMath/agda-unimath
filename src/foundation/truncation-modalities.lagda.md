# The truncation modalities

```agda
module foundation.truncation-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.truncations

open import foundation-core.dependent-pair-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The [truncation](foundation.truncations.md) operations are
[higher modalities](orthogonal-factorization-systems.higher-modalities.md).

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

### The truncation modalities are uniquely eliminating modalities

```agda
is-uniquely-eliminating-modality-trunc :
  {l : Level} {k : 𝕋} →
  is-uniquely-eliminating-modality (trunc-unit-modality {l} {k})
is-uniquely-eliminating-modality-trunc {k = k} A P =
  dependent-universal-property-trunc
    ( λ z → (type-trunc k (P z) , is-trunc-type-trunc))
```
