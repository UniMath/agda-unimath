# Rational commutative monoids

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.rational-commutative-monoids
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import group-theory.commutative-monoids funext univalence truncations
open import group-theory.monoids funext univalence truncations
open import group-theory.powers-of-elements-commutative-monoids funext univalence truncations
```

</details>

## Idea

A **rational commutative monoid** is a
[commutative monoid](group-theory.commutative-monoids.md) `(M,0,+)` in which the
map `x ↦ nx` is invertible for every
[natural number](elementary-number-theory.natural-numbers.md) `n > 0`. This
condition implies that we can invert the natural numbers in `M`, which are the
elements of the form `n1` in `M`.

Note: Since we usually write commutative monoids multiplicatively, the condition
that a commutative monoid is rational is that the map `x ↦ xⁿ` is invertible for
every natural number `n > 0`. However, for rational commutative monoids we will
write the binary operation additively.

## Definition

### The predicate of being a rational commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  is-rational-prop-Commutative-Monoid : Prop l
  is-rational-prop-Commutative-Monoid =
    Π-Prop ℕ
      ( λ n →
        is-equiv-Prop (power-Commutative-Monoid M (succ-ℕ n)))

  is-rational-Commutative-Monoid : UU l
  is-rational-Commutative-Monoid =
    type-Prop is-rational-prop-Commutative-Monoid

  is-prop-is-rational-Commutative-Monoid :
    is-prop is-rational-Commutative-Monoid
  is-prop-is-rational-Commutative-Monoid =
    is-prop-type-Prop is-rational-prop-Commutative-Monoid
```

### Rational commutative monoids

```agda
Rational-Commutative-Monoid : (l : Level) → UU (lsuc l)
Rational-Commutative-Monoid l =
  Σ (Commutative-Monoid l) is-rational-Commutative-Monoid

module _
  {l : Level} (M : Rational-Commutative-Monoid l)
  where

  commutative-monoid-Rational-Commutative-Monoid : Commutative-Monoid l
  commutative-monoid-Rational-Commutative-Monoid = pr1 M

  monoid-Rational-Commutative-Monoid : Monoid l
  monoid-Rational-Commutative-Monoid =
    monoid-Commutative-Monoid commutative-monoid-Rational-Commutative-Monoid

  type-Rational-Commutative-Monoid : UU l
  type-Rational-Commutative-Monoid =
    type-Commutative-Monoid commutative-monoid-Rational-Commutative-Monoid

  add-Rational-Commutative-Monoid :
    (x y : type-Rational-Commutative-Monoid) →
    type-Rational-Commutative-Monoid
  add-Rational-Commutative-Monoid =
    mul-Commutative-Monoid commutative-monoid-Rational-Commutative-Monoid

  zero-Rational-Commutative-Monoid : type-Rational-Commutative-Monoid
  zero-Rational-Commutative-Monoid =
    unit-Commutative-Monoid commutative-monoid-Rational-Commutative-Monoid

  associative-add-Rational-Commutative-Monoid :
    (x y z : type-Rational-Commutative-Monoid) →
    add-Rational-Commutative-Monoid
      ( add-Rational-Commutative-Monoid x y)
      ( z) ＝
    add-Rational-Commutative-Monoid
      ( x)
      ( add-Rational-Commutative-Monoid y z)
  associative-add-Rational-Commutative-Monoid =
    associative-mul-Commutative-Monoid
      commutative-monoid-Rational-Commutative-Monoid

  left-unit-law-add-Rational-Commutative-Monoid :
    (x : type-Rational-Commutative-Monoid) →
    add-Rational-Commutative-Monoid zero-Rational-Commutative-Monoid x ＝ x
  left-unit-law-add-Rational-Commutative-Monoid =
    left-unit-law-mul-Commutative-Monoid
      commutative-monoid-Rational-Commutative-Monoid

  right-unit-law-add-Rational-Commutative-Monoid :
    (x : type-Rational-Commutative-Monoid) →
    add-Rational-Commutative-Monoid x zero-Rational-Commutative-Monoid ＝ x
  right-unit-law-add-Rational-Commutative-Monoid =
    right-unit-law-mul-Commutative-Monoid
      commutative-monoid-Rational-Commutative-Monoid

  multiple-Rational-Commutative-Monoid :
    ℕ → type-Rational-Commutative-Monoid → type-Rational-Commutative-Monoid
  multiple-Rational-Commutative-Monoid =
    power-Commutative-Monoid commutative-monoid-Rational-Commutative-Monoid

  is-rational-Rational-Commutative-Monoid :
    is-rational-Commutative-Monoid
      commutative-monoid-Rational-Commutative-Monoid
  is-rational-Rational-Commutative-Monoid = pr2 M
```
