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
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.flat-discrete-crisp-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

We say a [dependent pair type](foundation.dependent-pair-types.md) is
{{#concept "crisp" Disambiguation="dependent pair type"}} if it is formed in a
[crisp context](modal-type-theory.crisp-types.md). Here, we study the
interactions between the [flat modality](modal-type-theory.flat-modality.md) and
[dependent pair types](foundation.dependent-pair-types.md).

## Definitions

```agda
Σ-♭ : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : @♭ A → UU l2) → UU (l1 ⊔ l2)
Σ-♭ A B = Σ (♭ A) (action-flat-crisp-family B)
```

## Properties

### Flat distributes over Σ-types

This is Lemma 6.8 of {{#cite Shu18}}.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-distributive-flat-Σ : ♭ (Σ A B) → Σ-♭ A (λ x → B x)
  pr1 (map-distributive-flat-Σ (intro-flat (x , y))) = intro-flat x
  pr2 (map-distributive-flat-Σ (intro-flat (x , y))) = intro-flat y

  map-inv-distributive-flat-Σ : Σ-♭ A (λ x → B x) → ♭ (Σ A B)
  map-inv-distributive-flat-Σ (intro-flat x , intro-flat y) = intro-flat (x , y)

  is-section-map-distributive-flat-Σ :
    is-section map-inv-distributive-flat-Σ map-distributive-flat-Σ
  is-section-map-distributive-flat-Σ (intro-flat _) = refl

  is-retraction-map-distributive-flat-Σ :
    is-retraction map-inv-distributive-flat-Σ map-distributive-flat-Σ
  is-retraction-map-distributive-flat-Σ (intro-flat _ , intro-flat _) = refl

  section-distributive-flat-Σ : section map-distributive-flat-Σ
  pr1 section-distributive-flat-Σ = map-inv-distributive-flat-Σ
  pr2 section-distributive-flat-Σ = is-retraction-map-distributive-flat-Σ

  retraction-distributive-flat-Σ : retraction map-distributive-flat-Σ
  pr1 retraction-distributive-flat-Σ = map-inv-distributive-flat-Σ
  pr2 retraction-distributive-flat-Σ = is-section-map-distributive-flat-Σ

  is-equiv-map-distributive-flat-Σ : is-equiv map-distributive-flat-Σ
  pr1 is-equiv-map-distributive-flat-Σ = section-distributive-flat-Σ
  pr2 is-equiv-map-distributive-flat-Σ = retraction-distributive-flat-Σ

  distributive-flat-Σ : ♭ (Σ A B) ≃ Σ-♭ A (λ x → B x)
  pr1 distributive-flat-Σ = map-distributive-flat-Σ
  pr2 distributive-flat-Σ = is-equiv-map-distributive-flat-Σ

  inv-distributive-flat-Σ : Σ-♭ A (λ x → B x) ≃ ♭ (Σ A B)
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
    ( map-Σ B counit-flat (λ where (intro-flat _) → counit-flat)) ∘
    ( map-distributive-flat-Σ)
  compute-counit-flat-Σ (intro-flat _) = refl
```

### A crisp dependent pair type over a flat discrete type is flat discrete if and only if the family is flat discrete

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  (is-disc-A : is-flat-discrete-crisp A)
  where

  is-flat-discrete-crisp-Σ :
    is-flat-discrete-crisp-family (λ x → B x) → is-flat-discrete-crisp (Σ A B)
  is-flat-discrete-crisp-Σ is-disc-B =
    is-equiv-left-map-triangle
      ( counit-flat)
      ( map-Σ B counit-flat (λ where (intro-flat _) → counit-flat))
      ( map-distributive-flat-Σ)
      ( λ where (intro-flat _) → refl)
      ( is-equiv-map-distributive-flat-Σ)
      ( is-equiv-map-Σ B is-disc-A (λ where (intro-flat x) → is-disc-B x))

  is-flat-discrete-crisp-family-is-flat-discrete-crisp-Σ :
    is-flat-discrete-crisp (Σ A B) → is-flat-discrete-crisp-family (λ x → B x)
  is-flat-discrete-crisp-family-is-flat-discrete-crisp-Σ is-disc-Σ-B x =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( B)
      ( counit-flat)
      ( λ where (intro-flat _) → counit-flat)
      ( is-disc-A)
      ( is-equiv-right-map-triangle
        ( counit-flat)
        ( _)
        ( map-distributive-flat-Σ)
        ( λ where (intro-flat _) → refl)
        ( is-disc-Σ-B)
        ( is-equiv-map-distributive-flat-Σ))
      ( intro-flat x)
```

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
