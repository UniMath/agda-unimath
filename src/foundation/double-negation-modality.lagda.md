# The double negation modality

```agda
module foundation.double-negation-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-negation
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.transport-along-identifications

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.types-local-at-maps
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

```agda
is-uniquely-eliminating-modality-double-negation-modality :
  {l : Level} →
  is-uniquely-eliminating-modality (unit-double-negation-modality {l})
is-uniquely-eliminating-modality-double-negation-modality {l} {A} P =
  is-local-dependent-type-is-prop
    ( unit-double-negation-modality)
    ( operator-double-negation-modality l ∘ P)
    ( λ _ → is-prop-double-negation)
    ( λ f z →
      double-negation-extend
        ( λ (a : A) →
          tr
            ( ¬¬_ ∘ P)
            ( eq-is-prop is-prop-double-negation)
            ( f a))
        ( z))
```

This proof follows Example 1.9 in {{#cite RSS20}}.

## References

{{#bibliography}}
