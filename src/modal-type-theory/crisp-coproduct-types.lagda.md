# Crisp coproduct types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.flat-discrete-crisp-types
open import modal-type-theory.flat-modality
```

</details>

## Idea

We say a [coproduct type](foundation-core.coproduct-types.md) is
{{#concept "crisp" Disambigiation="coproduct type"}} if it is formed in a crisp
context.

## Definitions

### Crisp case analysis

This is Theorem 5.4 of _Brouwer's fixed-point theorem in real-cohesive homotopy
type theory_, although the proof is much simpler.

```agda
crisp-ind-coprod :
  {@♭ l1 l2 l3 : Level}
  {@♭ A : UU l1} {@♭ B : UU l2} {@♭ C : @♭ A + B → UU l3} →
  @♭ ((@♭ x : A) → C (inl x)) →
  @♭ ((@♭ y : B) → C (inr y)) →
  ((@♭ u : A + B) → C u)
crisp-ind-coprod f g (inl x) = f x
crisp-ind-coprod f g (inr y) = g y

crisp-rec-coprod :
  {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ C : UU l3} →
  @♭ ((@♭ x : A) → C) →
  @♭ ((@♭ y : B) → C) →
  (@♭ (A + B) → C)
crisp-rec-coprod = crisp-ind-coprod
```

## Properties

### Flat distributes over coproduct types

This is Corollary 5.5 of _Brouwer's fixed-point theorem in real-cohesive
homotopy type theory_.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-distributive-flat-coprod : ♭ (A + B) → (♭ A) + (♭ B)
  map-distributive-flat-coprod (cons-flat (inl x)) = inl (cons-flat x)
  map-distributive-flat-coprod (cons-flat (inr x)) = inr (cons-flat x)

  map-inv-distributive-flat-coprod : (♭ A) + (♭ B) → ♭ (A + B)
  map-inv-distributive-flat-coprod (inl (cons-flat x)) = cons-flat (inl x)
  map-inv-distributive-flat-coprod (inr (cons-flat x)) = cons-flat (inr x)

  is-section-map-distributive-flat-coprod :
    is-section map-inv-distributive-flat-coprod map-distributive-flat-coprod
  is-section-map-distributive-flat-coprod (cons-flat (inl x)) = refl
  is-section-map-distributive-flat-coprod (cons-flat (inr x)) = refl

  is-retraction-map-distributive-flat-coprod :
    is-retraction map-inv-distributive-flat-coprod map-distributive-flat-coprod
  is-retraction-map-distributive-flat-coprod (inl (cons-flat x)) = refl
  is-retraction-map-distributive-flat-coprod (inr (cons-flat x)) = refl

  section-distributive-flat-coprod : section map-distributive-flat-coprod
  pr1 section-distributive-flat-coprod = map-inv-distributive-flat-coprod
  pr2 section-distributive-flat-coprod =
    is-retraction-map-distributive-flat-coprod

  retraction-distributive-flat-coprod : retraction map-distributive-flat-coprod
  pr1 retraction-distributive-flat-coprod = map-inv-distributive-flat-coprod
  pr2 retraction-distributive-flat-coprod =
    is-section-map-distributive-flat-coprod

  is-equiv-map-distributive-flat-coprod : is-equiv map-distributive-flat-coprod
  pr1 is-equiv-map-distributive-flat-coprod = section-distributive-flat-coprod
  pr2 is-equiv-map-distributive-flat-coprod =
    retraction-distributive-flat-coprod

  distributive-flat-coprod : ♭ (A + B) ≃ (♭ A) + (♭ B)
  pr1 distributive-flat-coprod = map-distributive-flat-coprod
  pr2 distributive-flat-coprod = is-equiv-map-distributive-flat-coprod

  inv-distributive-flat-coprod : (♭ A) + (♭ B) ≃ ♭ (A + B)
  inv-distributive-flat-coprod = inv-equiv distributive-flat-coprod
```

### Computing the flat counit on a coproduct type

The counit of the flat modality computes as the counit on each component of a
crisp dependent pair type.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  compute-counit-flat-coprod :
    counit-flat {A = A + B} ~
    ( ind-coprod _
      ( λ where (cons-flat x) → inl x)
      ( λ where (cons-flat x) → inr x)) ∘
    ( map-distributive-flat-coprod)
  compute-counit-flat-coprod (cons-flat (inl x)) = refl
  compute-counit-flat-coprod (cons-flat (inr x)) = refl
```

### A crisp coproduct type is flat discrete if both summands are

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  is-flat-discrete-crisp-coprod :
    is-flat-discrete-crisp A →
    is-flat-discrete-crisp B →
    is-flat-discrete-crisp (A + B)
  is-flat-discrete-crisp-coprod is-disc-A is-disc-B =
    is-equiv-left-map-triangle
      ( counit-flat)
      ( map-coprod counit-flat counit-flat)
      ( map-distributive-flat-coprod)
      ( λ where
        (cons-flat (inl x)) → refl
        (cons-flat (inr x)) → refl)
      ( is-equiv-map-distributive-flat-coprod)
      ( is-equiv-map-coprod is-disc-A is-disc-B)
```

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
