# The zero modality

```agda
module orthogonal-factorization-systems.zero-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.raising-universe-levels-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.types-local-at-maps
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The **zero modality** is the
[modality](orthogonal-factorization-systems.higher-modalities.md) that maps
every type to the [unit type](foundation.unit-type.md).

## Definition

```agda
operator-zero-modality :
  (l1 l2 : Level) → operator-modality l1 l2
operator-zero-modality l1 l2 _ = raise-unit l2

unit-zero-modality :
  {l1 l2 : Level} → unit-modality (operator-zero-modality l1 l2)
unit-zero-modality _ = raise-star
```

## Properties

### The zero modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-zero-modality :
  {l1 l2 : Level} →
  is-uniquely-eliminating-modality (unit-zero-modality {l1} {l2})
is-uniquely-eliminating-modality-zero-modality {l2 = l2} P =
  is-local-is-contr
    ( unit-zero-modality)
    ( raise-unit l2)
    ( is-contr-raise-unit)
```

### The zero modality is equivalent to `-2`-truncation

This remains to be made formal.
[#739](https://github.com/UniMath/agda-unimath/issues/739)
