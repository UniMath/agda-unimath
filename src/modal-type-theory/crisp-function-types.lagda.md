# Crisp function types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import modal-type-theory.crisp-dependent-function-types
open import modal-type-theory.flat-discrete-crisp-types
open import modal-type-theory.flat-modality
```

</details>

## Idea

We say a [function type](foundation-core.function-types.md) is
{{#concept "crisp" Disambigiation="function type"}} if it is formed in a crisp
context.

## Properties

### Flat distributes over dependent function types

```agda
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

- [Flat discrete types](modal-type-theory.flat-discrete-crisp-types.md) for
  types that are flat modal.

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
