# The zero modality

```agda
module orthogonal-factorization-systems.zero-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The **zero modality** is the
[modality](orthogonal-factorization-systems.higher-modalities.md) that maps
every type to the [unit type](foundation.unit-type.md).

## Definition

```agda
zero-operator-modality :
  (l1 l2 : Level) → operator-modality l1 l2
zero-operator-modality l1 l2 _ = raise-unit l2

zero-unit-modality :
  {l1 l2 : Level} → unit-modality (zero-operator-modality l1 l2)
zero-unit-modality _ = raise-star
```

## Properties

### The zero modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-zero :
  {l1 l2 : Level} →
  is-uniquely-eliminating-modality (zero-unit-modality {l1} {l2})
is-uniquely-eliminating-modality-zero {l2 = l2} A P =
  is-local-is-contr
    ( zero-unit-modality)
    ( raise-unit l2)
    ( is-contr-raise-unit)
```

### The zero modality is equivalent to `-2`-truncation

This remains to be made formal.
