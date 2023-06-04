# The double negation modality

```agda
module orthogonal-factorization-systems.double-negation-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.functions
open import foundation.negation
open import foundation.propositions
open import foundation.identity-types
open import foundation.double-negation
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The double negation operation `¬¬` is a modality. Its

## Definition

```agda
double-negation-operator-modality :
  {l : Level} → operator-modality l l
double-negation-operator-modality = ¬¬

double-negation-unit-modality :
  {l : Level} → unit-modality (double-negation-operator-modality {l})
double-negation-unit-modality = intro-double-negation
```

## Properties

### The double negation modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-double-negation :
  {l : Level} →
  is-uniquely-eliminating-modality (double-negation-unit-modality {l})
is-uniquely-eliminating-modality-double-negation A P =
  is-local-family-is-prop
    ( double-negation-unit-modality)
    ( double-negation-operator-modality ∘ P)
    ( λ _ → is-prop-double-negation)
    ( λ f z →
      double-negation-extend
        ( λ (a : A) →
          tr
            ( ¬¬ ∘ P)
            ( eq-is-prop is-prop-double-negation)
            ( f a))
        ( z))
```
