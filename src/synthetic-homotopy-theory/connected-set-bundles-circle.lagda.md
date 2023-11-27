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
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.mere-equality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import higher-group-theory.transitive-higher-group-actions

open import structured-types.sets-equipped-with-automorphisms

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

  set-connected-set-bundle-𝕊¹ : Set l
  set-connected-set-bundle-𝕊¹ =
    set-bundle-connected-set-bundle-𝕊¹ base-𝕊¹

  type-connected-set-bundle-𝕊¹ : UU l
  type-connected-set-bundle-𝕊¹ = type-Set set-connected-set-bundle-𝕊¹

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

  transitive-action-connected-set-bundle-𝕊¹ :
    transitive-action-∞-Group l 𝕊¹-∞-Group
  pr1 transitive-action-connected-set-bundle-𝕊¹ =
    bundle-connected-set-bundle-𝕊¹
  pr2 transitive-action-connected-set-bundle-𝕊¹ =
    is-connected-connected-set-bundle-𝕊¹

  is-abstractly-transitive-action-connected-set-bundle-𝕊¹ :
    is-abstractly-transitive-action-∞-Group
      ( 𝕊¹-∞-Group)
      ( bundle-connected-set-bundle-𝕊¹)
  is-abstractly-transitive-action-connected-set-bundle-𝕊¹ =
    is-abstractly-transitive-transitive-action-∞-Group
      ( 𝕊¹-∞-Group)
      ( transitive-action-connected-set-bundle-𝕊¹)

  is-inhabited-connected-set-bundle-𝕊¹ :
    is-inhabited type-connected-set-bundle-𝕊¹
  is-inhabited-connected-set-bundle-𝕊¹ =
    is-inhabited-transitive-action-∞-Group
      ( 𝕊¹-∞-Group)
      ( transitive-action-connected-set-bundle-𝕊¹)

  is-surjective-tr-connected-set-bundle-𝕊¹ :
    (t : 𝕊¹) (x : type-connected-set-bundle-𝕊¹) →
    is-surjective (λ (p : base-𝕊¹ ＝ t) → tr bundle-connected-set-bundle-𝕊¹ p x)
  is-surjective-tr-connected-set-bundle-𝕊¹ =
    is-surjective-tr-is-abstractly-transitive-action-∞-Group
      ( 𝕊¹-∞-Group)
      ( bundle-connected-set-bundle-𝕊¹)
      ( is-abstractly-transitive-action-connected-set-bundle-𝕊¹)

  inhabited-type-connected-set-bundle-𝕊¹ : Inhabited-Type l
  inhabited-type-connected-set-bundle-𝕊¹ =
    inhabited-type-transitive-action-∞-Group
      ( 𝕊¹-∞-Group)
      ( transitive-action-connected-set-bundle-𝕊¹)

  aut-connected-set-bundle-𝕊¹ : Aut type-connected-set-bundle-𝕊¹
  aut-connected-set-bundle-𝕊¹ =
    equiv-tr bundle-connected-set-bundle-𝕊¹ loop-𝕊¹

  map-aut-connected-set-bundle-𝕊¹ :
    type-connected-set-bundle-𝕊¹ → type-connected-set-bundle-𝕊¹
  map-aut-connected-set-bundle-𝕊¹ =
    map-equiv aut-connected-set-bundle-𝕊¹

  set-with-automorphism-connected-set-bundle-𝕊¹ : Set-With-Automorphism l
  pr1 set-with-automorphism-connected-set-bundle-𝕊¹ =
    set-connected-set-bundle-𝕊¹
  pr2 set-with-automorphism-connected-set-bundle-𝕊¹ =
    aut-connected-set-bundle-𝕊¹
```

## Properties

### Connected set bundles over the circle are cyclic sets

#### The set equipped with an automorphism obtained from a connected set bundle over the circle is a cyclic set

This remains to be shown.

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
