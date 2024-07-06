# The double negation modality

```agda
module foundation.double-negation-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-negation
open import foundation.universe-levels

open import foundation-core.empty-types

open import orthogonal-factorization-systems.continuation-modalities
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The [double negation](foundation.double-negation.md) operation `¬¬` is a
[modality](orthogonal-factorization-systems.higher-modalities.md).

## Definition

### The double negation modality

```agda
operator-double-negation-modality :
  (l : Level) → operator-modality l l
operator-double-negation-modality _ = ¬¬_

unit-double-negation-modality :
  {l : Level} → unit-modality (operator-double-negation-modality l)
unit-double-negation-modality = intro-double-negation
```

## Properties

### The double negation modality is a uniquely eliminating modality

The double negation modality is an instance of a
[continuation modality](orthogonal-factorization-systems.continuation-modalities.md).

```agda
is-uniquely-eliminating-modality-double-negation-modality :
  {l : Level} →
  is-uniquely-eliminating-modality (unit-double-negation-modality {l})
is-uniquely-eliminating-modality-double-negation-modality {l} =
  is-uniquely-eliminating-modality-continuation-modality l empty-Prop
```
