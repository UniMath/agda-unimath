# The truncation modalities

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.truncation-modalities
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.truncations funext univalence truncations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.truncation-levels

open import orthogonal-factorization-systems.modal-operators funext univalence truncations
open import orthogonal-factorization-systems.uniquely-eliminating-modalities funext univalence truncations
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
