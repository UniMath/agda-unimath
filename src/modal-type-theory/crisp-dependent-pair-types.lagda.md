# Crisp dependent pair types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.flat-modality
open import modal-type-theory.flat-discrete-crisp-types
```

</details>

## Idea

We say a dependent pair type is
{{#concept "crisp" Disambigiation="dependent pair type"}} if it is formed in a
crisp context. Here, we study the interactions between the
[flat modality](modal-type-theory.flat-modality.md) and
[dependent pair types](foundation.dependent-pair-types.md).

## Definitions

```agda
Σ-♭ : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : A → UU l2) → UU (l1 ⊔ l2)
Σ-♭ A B = Σ (♭ A) (λ where (cons-flat x) → ♭ (B x))
```

## Properties

### Flat distributes over Σ-types

This is Lemma 6.8 of _Brouwer's fixed-point theorem in real-cohesive homotopy
type theory_.

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

  is-equiv-map-distributive-flat-Σ : is-equiv map-distributive-flat-Σ
  pr1 is-equiv-map-distributive-flat-Σ = section-distributive-flat-Σ
  pr2 is-equiv-map-distributive-flat-Σ = retraction-distributive-flat-Σ

  distributive-flat-Σ : ♭ (Σ A B) ≃ Σ-♭ A B
  pr1 distributive-flat-Σ = map-distributive-flat-Σ
  pr2 distributive-flat-Σ = is-equiv-map-distributive-flat-Σ

  inv-distributive-flat-Σ : Σ-♭ A B ≃ ♭ (Σ A B)
  inv-distributive-flat-Σ = inv-equiv distributive-flat-Σ
```

### Computing the flat counit on a dependent pair type

The counit of the flat modality computes as the counit on each component of a
crisp dependent pair type.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  compute-counit-flat-Σ :
    counit-flat {A = Σ A B} ~
    ( map-Σ B counit-flat (λ where (cons-flat _) → counit-flat)) ∘
    ( map-distributive-flat-Σ)
  compute-counit-flat-Σ (cons-flat _) = refl
```

### A crisp dependent pair type over a flat discrete type is flat discrete if and only if the family is flat discrete

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  (is-flat-A : is-flat-discrete-crisp A)
  where

  is-flat-discrete-crisp-Σ :
    is-flat-discrete-crisp-family (λ x → B x) → is-flat-discrete-crisp (Σ A B)
  is-flat-discrete-crisp-Σ is-flat-B =
    is-equiv-left-map-triangle
      ( counit-flat)
      ( map-Σ B counit-flat (λ where (cons-flat _) → counit-flat))
      ( map-distributive-flat-Σ)
      ( λ where (cons-flat _) → refl)
      ( is-equiv-map-distributive-flat-Σ)
      ( is-equiv-map-Σ B is-flat-A (λ where (cons-flat x) → is-flat-B x))

  is-flat-discrete-crisp-family-is-flat-discrete-crisp-Σ :
    is-flat-discrete-crisp (Σ A B) → is-flat-discrete-crisp-family (λ x → B x)
  is-flat-discrete-crisp-family-is-flat-discrete-crisp-Σ is-flat-Σ-B x =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( B)
      ( counit-flat)
      ( λ where (cons-flat _) → counit-flat)
      ( is-flat-A)
      ( is-equiv-right-map-triangle
        ( counit-flat)
        ( _)
        ( map-distributive-flat-Σ)
        ( λ where (cons-flat _) → refl)
        ( is-flat-Σ-B)
        ( is-equiv-map-distributive-flat-Σ))
      ( cons-flat x)
```

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
