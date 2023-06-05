# The trivial modality

```agda
module orthogonal-factorization-systems.trivial-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.functions
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The identity operation on types is trivially a
[higher modality](orthogonal-factorization-systems.higher-modalities.md), which
we call the **trivial modality**.

## Definition

```agda
id-operator-modality :
  (l : Level) → operator-modality l l
id-operator-modality l = id

id-unit-modality :
  {l : Level} → unit-modality (id-operator-modality l)
id-unit-modality = id
```

## Properties

### The trivial modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-id :
  {l : Level} → is-uniquely-eliminating-modality (id-unit-modality {l})
is-uniquely-eliminating-modality-id {l} _ P =
  is-local-family-is-equiv
    ( id-unit-modality)
    ( is-equiv-id)
    ( id-operator-modality l ∘ P)
```
