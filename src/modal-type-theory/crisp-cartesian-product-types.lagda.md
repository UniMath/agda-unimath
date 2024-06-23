# Crisp cartesian product types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.flat-discrete-crisp-types
open import modal-type-theory.flat-modality
```

</details>

## Idea

We say a [cartesian product type](foundation-core.cartesian-product-types.md) is
{{#concept "crisp" Disambiguation="cartesian product type"}} if it is formed in
a [crisp context](modal-type-theory.crisp-types.md).

## Properties

### Flat distributes over cartesian product types

This is Theorem 6.9 of {{#cite Shu18}}.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-distributive-flat-product : ♭ (A × B) → ♭ A × ♭ B
  pr1 (map-distributive-flat-product (intro-flat (x , y))) = intro-flat x
  pr2 (map-distributive-flat-product (intro-flat (x , y))) = intro-flat y

  map-inv-distributive-flat-product : ♭ A × ♭ B → ♭ (A × B)
  map-inv-distributive-flat-product (intro-flat x , intro-flat y) =
    intro-flat (x , y)

  is-section-map-distributive-flat-product :
    is-section map-inv-distributive-flat-product map-distributive-flat-product
  is-section-map-distributive-flat-product (intro-flat x) = refl

  is-retraction-map-distributive-flat-product :
    is-retraction
      ( map-inv-distributive-flat-product)
      ( map-distributive-flat-product)
  is-retraction-map-distributive-flat-product (intro-flat x , intro-flat y) =
    refl

  section-distributive-flat-product : section map-distributive-flat-product
  pr1 section-distributive-flat-product = map-inv-distributive-flat-product
  pr2 section-distributive-flat-product =
    is-retraction-map-distributive-flat-product

  retraction-distributive-flat-product :
    retraction map-distributive-flat-product
  pr1 retraction-distributive-flat-product = map-inv-distributive-flat-product
  pr2 retraction-distributive-flat-product =
    is-section-map-distributive-flat-product

  is-equiv-map-distributive-flat-product :
    is-equiv map-distributive-flat-product
  pr1 is-equiv-map-distributive-flat-product = section-distributive-flat-product
  pr2 is-equiv-map-distributive-flat-product =
    retraction-distributive-flat-product

  distributive-flat-product : ♭ (A × B) ≃ ♭ A × ♭ B
  pr1 distributive-flat-product = map-distributive-flat-product
  pr2 distributive-flat-product = is-equiv-map-distributive-flat-product

  inv-distributive-flat-product : ♭ A × ♭ B ≃ ♭ (A × B)
  inv-distributive-flat-product = inv-equiv distributive-flat-product
```

### Computing the flat counit on a cartesian product type

The counit of the flat modality computes as the counit on each component of a
crisp dependent pair type.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  compute-counit-flat-product :
    counit-flat {A = A × B} ~
    ( map-product counit-flat counit-flat ∘ map-distributive-flat-product)
  compute-counit-flat-product (intro-flat x) = refl
```

### Flat discrete crisp types are closed under cartesian products

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  is-flat-discrete-crisp-product :
    is-flat-discrete-crisp A →
    is-flat-discrete-crisp B →
    is-flat-discrete-crisp (A × B)
  is-flat-discrete-crisp-product is-disc-A is-disc-B =
    is-equiv-left-map-triangle
      ( counit-flat)
      ( map-product counit-flat counit-flat)
      ( map-distributive-flat-product)
      ( λ where (intro-flat _) → refl)
      ( is-equiv-map-distributive-flat-product)
      ( is-equiv-map-product counit-flat counit-flat is-disc-A is-disc-B)
```

### A factor is a flat discrete crisp type if the cartesian product is a flat discrete crisp type and the other factor is inhabited

```agda
  is-flat-discrete-crisp-right-factor-product' :
    is-flat-discrete-crisp (A × B) → A → is-flat-discrete-crisp B
  is-flat-discrete-crisp-right-factor-product'
    is-disc-product-A-B x =
    is-equiv-right-factor-is-equiv-map-product'
      ( counit-flat)
      ( counit-flat)
      ( x)
      ( is-equiv-right-map-triangle
        counit-flat
        ( map-product counit-flat counit-flat)
        ( map-distributive-flat-product)
        ( λ where (intro-flat _) → refl)
        ( is-disc-product-A-B)
        ( is-equiv-map-distributive-flat-product))

  is-flat-discrete-crisp-right-factor-product :
    is-flat-discrete-crisp (A × B) → is-inhabited A → is-flat-discrete-crisp B
  is-flat-discrete-crisp-right-factor-product
    is-disc-product-A-B =
    rec-trunc-Prop
      ( is-flat-discrete-crisp-Prop B)
      ( is-flat-discrete-crisp-right-factor-product' is-disc-product-A-B)

  is-flat-discrete-crisp-left-factor-product' :
    is-flat-discrete-crisp (A × B) → B → is-flat-discrete-crisp A
  is-flat-discrete-crisp-left-factor-product'
    is-disc-product-A-B x =
    is-equiv-left-factor-is-equiv-map-product'
      ( counit-flat)
      ( counit-flat)
      ( x)
      ( is-equiv-right-map-triangle
        counit-flat
        ( map-product counit-flat counit-flat)
        ( map-distributive-flat-product)
        ( λ where (intro-flat _) → refl)
        ( is-disc-product-A-B)
        ( is-equiv-map-distributive-flat-product))

  is-flat-discrete-crisp-left-factor-product :
    is-flat-discrete-crisp (A × B) → is-inhabited B → is-flat-discrete-crisp A
  is-flat-discrete-crisp-left-factor-product
    is-disc-product-A-B =
    rec-trunc-Prop
      ( is-flat-discrete-crisp-Prop A)
      ( is-flat-discrete-crisp-left-factor-product' is-disc-product-A-B)
```

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
