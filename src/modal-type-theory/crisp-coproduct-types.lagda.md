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
{{#concept "crisp" Disambiguation="coproduct type"}} if it is formed in a
[crisp context](modal-type-theory.crisp-types.md).

## Definitions

### Crisp case analysis

This is Theorem 5.4 of {{#cite Shu18}}, although the proof is much simpler.

```agda
crisp-ind-coproduct :
  {@♭ l1 l2 l3 : Level}
  {@♭ A : UU l1} {@♭ B : UU l2} {@♭ C : @♭ A + B → UU l3} →
  @♭ ((@♭ x : A) → C (inl x)) →
  @♭ ((@♭ y : B) → C (inr y)) →
  ((@♭ u : A + B) → C u)
crisp-ind-coproduct f g (inl x) = f x
crisp-ind-coproduct f g (inr y) = g y

crisp-rec-coproduct :
  {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ C : UU l3} →
  @♭ ((@♭ x : A) → C) →
  @♭ ((@♭ y : B) → C) →
  (@♭ (A + B) → C)
crisp-rec-coproduct = crisp-ind-coproduct
```

## Properties

### Flat distributes over coproduct types

This is Corollary 5.5 of {{#cite Shu18}}.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-distributive-flat-coproduct : ♭ (A + B) → ♭ A + ♭ B
  map-distributive-flat-coproduct (intro-flat (inl x)) = inl (intro-flat x)
  map-distributive-flat-coproduct (intro-flat (inr x)) = inr (intro-flat x)

  map-inv-distributive-flat-coproduct : ♭ A + ♭ B → ♭ (A + B)
  map-inv-distributive-flat-coproduct (inl (intro-flat x)) = intro-flat (inl x)
  map-inv-distributive-flat-coproduct (inr (intro-flat x)) = intro-flat (inr x)

  is-section-map-distributive-flat-coproduct :
    is-section
      ( map-inv-distributive-flat-coproduct)
      ( map-distributive-flat-coproduct)
  is-section-map-distributive-flat-coproduct (intro-flat (inl x)) = refl
  is-section-map-distributive-flat-coproduct (intro-flat (inr x)) = refl

  is-retraction-map-distributive-flat-coproduct :
    is-retraction
      ( map-inv-distributive-flat-coproduct)
      ( map-distributive-flat-coproduct)
  is-retraction-map-distributive-flat-coproduct (inl (intro-flat x)) = refl
  is-retraction-map-distributive-flat-coproduct (inr (intro-flat x)) = refl

  section-distributive-flat-coproduct : section map-distributive-flat-coproduct
  pr1 section-distributive-flat-coproduct = map-inv-distributive-flat-coproduct
  pr2 section-distributive-flat-coproduct =
    is-retraction-map-distributive-flat-coproduct

  retraction-distributive-flat-coproduct :
    retraction map-distributive-flat-coproduct
  pr1 retraction-distributive-flat-coproduct =
    map-inv-distributive-flat-coproduct
  pr2 retraction-distributive-flat-coproduct =
    is-section-map-distributive-flat-coproduct

  is-equiv-map-distributive-flat-coproduct :
    is-equiv map-distributive-flat-coproduct
  pr1 is-equiv-map-distributive-flat-coproduct =
    section-distributive-flat-coproduct
  pr2 is-equiv-map-distributive-flat-coproduct =
    retraction-distributive-flat-coproduct

  distributive-flat-coproduct : ♭ (A + B) ≃ ♭ A + ♭ B
  pr1 distributive-flat-coproduct = map-distributive-flat-coproduct
  pr2 distributive-flat-coproduct = is-equiv-map-distributive-flat-coproduct

  inv-distributive-flat-coproduct : ♭ A + ♭ B ≃ ♭ (A + B)
  inv-distributive-flat-coproduct = inv-equiv distributive-flat-coproduct
```

### Computing the flat counit on a coproduct type

The counit of the flat modality computes as the counit on each component of a
crisp dependent pair type.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  compute-counit-flat-coproduct :
    counit-flat {A = A + B} ~
    map-coproduct counit-flat counit-flat ∘ map-distributive-flat-coproduct
  compute-counit-flat-coproduct (intro-flat (inl x)) = refl
  compute-counit-flat-coproduct (intro-flat (inr x)) = refl
```

### A crisp coproduct type is flat discrete if both summands are

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  abstract
    is-flat-discrete-crisp-coproduct :
      is-flat-discrete-crisp A →
      is-flat-discrete-crisp B →
      is-flat-discrete-crisp (A + B)
    is-flat-discrete-crisp-coproduct is-disc-A is-disc-B =
      is-equiv-left-map-triangle
        ( counit-flat)
        ( map-coproduct counit-flat counit-flat)
        ( map-distributive-flat-coproduct)
        ( λ where
          (intro-flat (inl x)) → refl
          (intro-flat (inr x)) → refl)
        ( is-equiv-map-distributive-flat-coproduct)
        ( is-equiv-map-coproduct is-disc-A is-disc-B)
```

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
