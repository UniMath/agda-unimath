# The flat-sharp adjunction

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-sharp-adjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.induction-modalities
open import orthogonal-factorization-systems.locally-small-modal-operators
open import modal-type-theory.sharp-modality
open import modal-type-theory.flat-modality
open import modal-type-theory.codiscrete-types
```

</details>

## Idea

We postulate that

## Postulates

```agda
postulate
  crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} → @♭ ♯ A → A

  compute-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) → (crisp-elim-♯ (unit-♯ x)) ＝ x

  uniqueness-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : ♯ A) → unit-♯ (crisp-elim-♯ x) ＝ x

  coherence-uniqueness-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) →
    uniqueness-crisp-elim-♯ (unit-♯ x) ＝ ap unit-♯ (compute-crisp-elim-♯ x)
```

## See also

- In [codiscrete types](modal-type-theory.codiscrete-types.md), we postulate
  that the sharp modality is a
  [higher modality](orthogonal-factorization-systems.higher-modalities.md).

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
