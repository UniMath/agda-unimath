# Commuting elements of monoids

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.commuting-elements-monoids
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

open import group-theory.commuting-elements-semigroups funext univalence
open import group-theory.monoids funext univalence truncations
```

</details>

## Idea

Two elements `x` and `y` of a [monoid](group-theory.monoids.md) `G` are said to
**commute** if the equality `xy ＝ yx` holds.

## Definitions

### Commuting elements

```agda
module _
  {l : Level} (M : Monoid l)
  where

  commute-prop-Monoid : (x y : type-Monoid M) → Prop l
  commute-prop-Monoid = commute-prop-Semigroup (semigroup-Monoid M)

  commute-Monoid : (x y : type-Monoid M) → UU l
  commute-Monoid = commute-Semigroup (semigroup-Monoid M)

  commute-Monoid' : (x y : type-Monoid M) → UU l
  commute-Monoid' = commute-Semigroup' (semigroup-Monoid M)

  is-prop-commute-Monoid : (x y : type-Monoid M) → is-prop (commute-Monoid x y)
  is-prop-commute-Monoid = is-prop-commute-Semigroup (semigroup-Monoid M)
```

## Properties

### The relation `commute-Monoid` is reflexive

```agda
module _
  {l : Level} (M : Monoid l)
  where

  refl-commute-Monoid : (x : type-Monoid M) → commute-Monoid M x x
  refl-commute-Monoid = refl-commute-Semigroup (semigroup-Monoid M)
```

### The relation `commute-Monoid` is symmetric

```agda
module _
  {l : Level} (M : Monoid l)
  where

  symmetric-commute-Monoid :
    (x y : type-Monoid M) → commute-Monoid M x y → commute-Monoid M y x
  symmetric-commute-Monoid = symmetric-commute-Semigroup (semigroup-Monoid M)
```

### The unit element commutes with every element of the monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  commute-unit-Monoid : (x : type-Monoid M) → commute-Monoid M x (unit-Monoid M)
  commute-unit-Monoid x =
    right-unit-law-mul-Monoid M x ∙ inv (left-unit-law-mul-Monoid M x)
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  private
    infix 45 _*_
    _*_ = mul-Monoid M

  left-swap-commute-Monoid :
    (x y z : type-Monoid M) → commute-Monoid M x y →
    x * (y * z) ＝ y * (x * z)
  left-swap-commute-Monoid = left-swap-commute-Semigroup (semigroup-Monoid M)

  right-swap-commute-Monoid :
    (x y z : type-Monoid M) → commute-Monoid M y z →
    (x * y) * z ＝ (x * z) * y
  right-swap-commute-Monoid = right-swap-commute-Semigroup (semigroup-Monoid M)
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  commute-mul-Monoid :
    (x y z : type-Monoid M) →
    commute-Monoid M x y → commute-Monoid M x z →
    commute-Monoid M x (mul-Monoid M y z)
  commute-mul-Monoid = commute-mul-Semigroup (semigroup-Monoid M)
```
