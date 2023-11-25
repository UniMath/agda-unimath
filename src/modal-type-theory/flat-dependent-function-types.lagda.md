# Flat dependent function types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.flat-modality
```

</details>

## Idea

We study interactions between the
[flat modality](modal-type-theory.flat-modality.md) and
[dependent function types](foundation.function-types.md).

## Properties

### Flat distributes over dependent function types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-crisp-distributive-flat-Π : ♭ ((x : A) → B x) → ((@♭ x : A) → ♭ (B x))
  map-crisp-distributive-flat-Π (cons-flat f) x = cons-flat (f x)

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-crisp-distributive-flat-function-types : ♭ (A → B) → (@♭ A → ♭ B)
  map-crisp-distributive-flat-function-types = map-crisp-distributive-flat-Π

  map-distributive-flat-function-types : ♭ (A → B) → (♭ A → ♭ B)
  map-distributive-flat-function-types f (cons-flat x) =
    map-crisp-distributive-flat-function-types f x
```

## See also

- [Flat discrete types](modal-type-theory.flat-discrete-types.md) for types that
  are flat modal.

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
