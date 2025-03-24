# Central elements of monoids

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.central-elements-monoids
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import group-theory.central-elements-semigroups funext univalence
open import group-theory.monoids funext univalence truncations
```

</details>

## Idea

An element `x` of a monoid `M` is said to be central if `xy ＝ yx` for every
`y : M`.

## Definition

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-central-element-prop-Monoid : type-Monoid M → Prop l
  is-central-element-prop-Monoid =
    is-central-element-prop-Semigroup (semigroup-Monoid M)

  is-central-element-Monoid : type-Monoid M → UU l
  is-central-element-Monoid =
    is-central-element-Semigroup (semigroup-Monoid M)

  is-prop-is-central-element-Monoid :
    (x : type-Monoid M) → is-prop (is-central-element-Monoid x)
  is-prop-is-central-element-Monoid =
    is-prop-is-central-element-Semigroup (semigroup-Monoid M)
```

## Properties

### The unit element is central

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-central-element-unit-Monoid : is-central-element-Monoid M (unit-Monoid M)
  is-central-element-unit-Monoid y =
    left-unit-law-mul-Monoid M y ∙ inv (right-unit-law-mul-Monoid M y)
```

### The product of two central elements is central

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-central-element-mul-Monoid :
    (x y : type-Monoid M) →
    is-central-element-Monoid M x → is-central-element-Monoid M y →
    is-central-element-Monoid M (mul-Monoid M x y)
  is-central-element-mul-Monoid =
    is-central-element-mul-Semigroup (semigroup-Monoid M)
```
