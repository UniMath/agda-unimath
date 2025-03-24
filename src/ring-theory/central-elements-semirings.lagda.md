# Central elements of semirings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.central-elements-semirings
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

open import group-theory.central-elements-monoids funext univalence truncations

open import ring-theory.semirings funext univalence truncations
```

</details>

## Idea

An element `x` of a semiring `R` is said to be central if `xy ＝ yx` for every
`y : R`.

## Definition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-central-element-semiring-Prop : type-Semiring R → Prop l
  is-central-element-semiring-Prop =
    is-central-element-prop-Monoid
      ( multiplicative-monoid-Semiring R)

  is-central-element-Semiring : type-Semiring R → UU l
  is-central-element-Semiring =
    is-central-element-Monoid (multiplicative-monoid-Semiring R)

  is-prop-is-central-element-Semiring :
    (x : type-Semiring R) → is-prop (is-central-element-Semiring x)
  is-prop-is-central-element-Semiring =
    is-prop-is-central-element-Monoid (multiplicative-monoid-Semiring R)
```

## Properties

### The zero element is central

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-central-element-zero-Semiring :
    is-central-element-Semiring R (zero-Semiring R)
  is-central-element-zero-Semiring x =
    left-zero-law-mul-Semiring R x ∙ inv (right-zero-law-mul-Semiring R x)
```

### The unit element is central

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-central-element-one-Semiring :
    is-central-element-Semiring R (one-Semiring R)
  is-central-element-one-Semiring =
    is-central-element-unit-Monoid (multiplicative-monoid-Semiring R)
```

### The sum of two central elements is central

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-central-element-add-Semiring :
    (x y : type-Semiring R) → is-central-element-Semiring R x →
    is-central-element-Semiring R y →
    is-central-element-Semiring R (add-Semiring R x y)
  is-central-element-add-Semiring x y H K z =
    ( right-distributive-mul-add-Semiring R x y z) ∙
    ( ( ap-add-Semiring R (H z) (K z)) ∙
      ( inv (left-distributive-mul-add-Semiring R z x y)))
```

### The product of two central elements is central

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-central-element-mul-Semiring :
    (x y : type-Semiring R) →
    is-central-element-Semiring R x → is-central-element-Semiring R y →
    is-central-element-Semiring R (mul-Semiring R x y)
  is-central-element-mul-Semiring =
    is-central-element-mul-Monoid (multiplicative-monoid-Semiring R)
```
