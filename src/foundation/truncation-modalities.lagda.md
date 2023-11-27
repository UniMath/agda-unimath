# The truncation modalities

```agda
module foundation.truncation-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.truncations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.truncation-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The [truncation](foundation.truncations.md) operations are
[higher modalities](orthogonal-factorization-systems.higher-modalities.md).

## Definition

```agda
operator-trunc-modality :
  (l : Level) (k : 𝕋) → operator-modality l l
operator-trunc-modality _ = type-trunc

unit-trunc-modality :
  {l : Level} {k : 𝕋} → unit-modality (operator-trunc-modality l k)
unit-trunc-modality = unit-trunc
```

## Properties

### The truncation modalities are uniquely eliminating modalities

```agda
is-uniquely-eliminating-modality-trunc-modality :
  {l : Level} {k : 𝕋} →
  is-uniquely-eliminating-modality (unit-trunc-modality {l} {k})
is-uniquely-eliminating-modality-trunc-modality {k = k} P =
  dependent-universal-property-trunc (trunc k ∘ P)
```
