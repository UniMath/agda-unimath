# Connected set bundles over the circle

```agda
module synthetic-homotopy-theory.connected-set-bundles-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.circle
```

</details>

## Idea

A **connected set bundle** over the
[circle](synthetic-homotopy-theory.circle.md) is a family of sets `X : 𝕊¹ → Set`
such that the total space `Σ 𝕊¹ (type-Set ∘ X)` is
[connected](foundation.connected-types.md). The connected set bundles over the
circle form a [large category](category-theory.large-categories.md), which can
be thought of as the categorification of the [poset](order-theory.posets.md) of
[natural numbers ordered by divisibility](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).

## Definitions

### The predicate of being a connected set bundle over the circle

```agda
is-connected-prop-set-bundle-𝕊¹ :
  {l : Level} → (𝕊¹ → Set l) → Prop l
is-connected-prop-set-bundle-𝕊¹ X =
  is-0-connected-Prop (Σ 𝕊¹ (type-Set ∘ X))

is-connected-set-bundle-𝕊¹ : {l : Level} (X : 𝕊¹ → Set l) → UU l
is-connected-set-bundle-𝕊¹ X =
  type-Prop (is-connected-prop-set-bundle-𝕊¹ X)

is-prop-is-connected-set-bundle-𝕊¹ :
  {l : Level} (X : 𝕊¹ → Set l) → is-prop (is-connected-set-bundle-𝕊¹ X)
is-prop-is-connected-set-bundle-𝕊¹ X =
  is-prop-type-Prop (is-connected-prop-set-bundle-𝕊¹ X)
```

### Connected set bundles over the circle

```agda
connected-set-bundle-𝕊¹ : (l : Level) → UU (lsuc l)
connected-set-bundle-𝕊¹ l = type-subtype is-connected-prop-set-bundle-𝕊¹

module _
  {l : Level} (X : connected-set-bundle-𝕊¹ l)
  where

  set-bundle-connected-set-bundle-𝕊¹ : 𝕊¹ → Set l
  set-bundle-connected-set-bundle-𝕊¹ = pr1 X

  bundle-connected-set-bundle-𝕊¹ : 𝕊¹ → UU l
  bundle-connected-set-bundle-𝕊¹ =
    type-Set ∘ set-bundle-connected-set-bundle-𝕊¹

  total-space-connected-set-bundle-𝕊¹ : UU l
  total-space-connected-set-bundle-𝕊¹ = Σ 𝕊¹ bundle-connected-set-bundle-𝕊¹

  is-connected-connected-set-bundle-𝕊¹ :
    is-connected-set-bundle-𝕊¹ set-bundle-connected-set-bundle-𝕊¹
  is-connected-connected-set-bundle-𝕊¹ = pr2 X

  mere-eq-total-space-connected-set-bundle-𝕊¹ :
    (x y : total-space-connected-set-bundle-𝕊¹) →
    mere-eq x y
  mere-eq-total-space-connected-set-bundle-𝕊¹ =
    mere-eq-is-0-connected is-connected-connected-set-bundle-𝕊¹

  set-connected-set-bundle-𝕊¹ : Set l
  set-connected-set-bundle-𝕊¹ =
    set-bundle-connected-set-bundle-𝕊¹ base-𝕊¹

  type-connected-set-bundle-𝕊¹ : UU l
  type-connected-set-bundle-𝕊¹ = type-Set set-connected-set-bundle-𝕊¹

  abstract
    is-inhabited-type-connected-set-bundle-𝕊¹ :
      is-inhabited type-connected-set-bundle-𝕊¹
    is-inhabited-type-connected-set-bundle-𝕊¹ =
      apply-universal-property-trunc-Prop
        ( is-inhabited-is-0-connected is-connected-connected-set-bundle-𝕊¹)
        ( trunc-Prop type-connected-set-bundle-𝕊¹)
        ( λ (t , x) →
          apply-universal-property-trunc-Prop
            ( mere-eq-𝕊¹ base-𝕊¹ t)
            ( trunc-Prop type-connected-set-bundle-𝕊¹)
            ( λ { refl → unit-trunc-Prop x}))

  inhabited-type-connected-set-bundle-𝕊¹ : Inhabited-Type l
  pr1 inhabited-type-connected-set-bundle-𝕊¹ =
    type-connected-set-bundle-𝕊¹
  pr2 inhabited-type-connected-set-bundle-𝕊¹ =
    is-inhabited-type-connected-set-bundle-𝕊¹

  aut-connected-set-bundle-𝕊¹ : Aut type-connected-set-bundle-𝕊¹
  aut-connected-set-bundle-𝕊¹ =
    equiv-tr bundle-connected-set-bundle-𝕊¹ loop-𝕊¹

  map-aut-connected-set-bundle-𝕊¹ :
    type-connected-set-bundle-𝕊¹ → type-connected-set-bundle-𝕊¹
  map-aut-connected-set-bundle-𝕊¹ =
    map-equiv aut-connected-set-bundle-𝕊¹
```

## Properties

### Connected set bundles over the circle are cyclic types

This remains to be formalized
