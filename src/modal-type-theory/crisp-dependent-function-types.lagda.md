# Crisp dependent function types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

We say a dependent function type is
{{#concept "crisp" Disambigiation="dependent function type"}} if it is formed in
a crisp context.

## Properties

### Flat distributes over dependent function types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  where

  map-distributive-flat-crisp-Π : ♭ ((@♭ x : A) → B x) → ((@♭ x : A) → ♭ (B x))
  map-distributive-flat-crisp-Π (cons-flat f) x = cons-flat (f x)

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-distributive-flat-Π :
    ♭ ((x : A) → B x) → ((x : ♭ A) → flat-family B x)
  map-distributive-flat-Π (cons-flat f) (cons-flat x) = cons-flat (f x)
```

## See also

- [Flat discrete types](modal-type-theory.flat-discrete-crisp-types.md) for
  types that are flat modal.

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
