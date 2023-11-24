# Flat dependent pair types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-dependent-pair-types where
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
[dependent pair types](foundation.dependent-pair-types.md).

## Definitions

```agda
Σ-♭ : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : A → UU l2) → UU (l1 ⊔ l2)
Σ-♭ A B = Σ (♭ A) (λ where (cons-flat x) → ♭ (B x))
```

## Properties

### Flat distributes over Σ-types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-distributive-flat-Σ : ♭ (Σ A B) → Σ-♭ A B
  pr1 (map-distributive-flat-Σ (cons-flat (x , y))) = cons-flat x
  pr2 (map-distributive-flat-Σ (cons-flat (x , y))) = cons-flat y

  map-inv-distributive-flat-Σ : Σ-♭ A B → ♭ (Σ A B)
  map-inv-distributive-flat-Σ (cons-flat x , cons-flat y) = cons-flat (x , y)

  is-section-distributive-flat-Σ :
    (map-inv-distributive-flat-Σ ∘ map-distributive-flat-Σ) ~ id
  is-section-distributive-flat-Σ (cons-flat _) = refl

  is-retraction-distributive-flat-Σ :
    (map-distributive-flat-Σ ∘ map-inv-distributive-flat-Σ) ~ id
  is-retraction-distributive-flat-Σ (cons-flat _ , cons-flat _) = refl

  section-distributive-flat-Σ : section map-distributive-flat-Σ
  pr1 section-distributive-flat-Σ = map-inv-distributive-flat-Σ
  pr2 section-distributive-flat-Σ = is-retraction-distributive-flat-Σ

  retraction-distributive-flat-Σ : retraction map-distributive-flat-Σ
  pr1 retraction-distributive-flat-Σ = map-inv-distributive-flat-Σ
  pr2 retraction-distributive-flat-Σ = is-section-distributive-flat-Σ

  is-equiv-distributive-flat-Σ : is-equiv map-distributive-flat-Σ
  pr1 is-equiv-distributive-flat-Σ = section-distributive-flat-Σ
  pr2 is-equiv-distributive-flat-Σ = retraction-distributive-flat-Σ

  equiv-distributive-flat-Σ : ♭ (Σ A B) ≃ Σ-♭ A B
  pr1 equiv-distributive-flat-Σ = map-distributive-flat-Σ
  pr2 equiv-distributive-flat-Σ = is-equiv-distributive-flat-Σ

  inv-equiv-distributive-flat-Σ : Σ-♭ A B ≃ ♭ (Σ A B)
  inv-equiv-distributive-flat-Σ = inv-equiv equiv-distributive-flat-Σ
```

## See also

- [Flat discrete types](modal-type-theory.flat-discrete-types.md) for types that
  are flat modal.

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
