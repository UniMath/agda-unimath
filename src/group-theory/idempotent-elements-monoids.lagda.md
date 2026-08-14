# Idempotent elements of monoids

```agda
module group-theory.idempotent-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.idempotent-elements-semigroups
open import group-theory.monoids
open import group-theory.powers-of-elements-monoids
```

</details>

## Idea

An {{#concept "idempotent element" Disambiguation="monoid" Agda=is-idempotent-element-Monoid}} of a [monoid](group-theory.monoids.md) is an element `x` satisfying

```text
  x² ＝ x.
```

## Definitions

### The predicate of being an idempotent element

```agda
module _
  {l1 : Level} (M : Monoid l1)
  where

  is-idempotent-element-Monoid : type-Monoid M → UU l1
  is-idempotent-element-Monoid =
    is-idempotent-element-Semigroup (semigroup-Monoid M)

  is-prop-is-idempotent-element-Monoid :
    (x : type-Monoid M) → is-prop (is-idempotent-element-Monoid x)
  is-prop-is-idempotent-element-Monoid =
    is-prop-is-idempotent-element-Semigroup (semigroup-Monoid M)

  is-idempotent-element-prop-Monoid :
    type-Monoid M → Prop l1
  is-idempotent-element-prop-Monoid =
    is-idempotent-element-prop-Semigroup (semigroup-Monoid M)
```

## Properties

### If `x` is idempotent, then `xⁿ ＝ x` for all `n ≥ 1`

```agda
module _
  {l1 : Level} (M : Monoid l1) {x : type-Monoid M}
  where

  compute-power-succ-is-idempotent-element-Monoid :
    is-idempotent-element-Monoid M x →
    (n : ℕ) → power-Monoid M (succ-ℕ n) x ＝ x
  compute-power-succ-is-idempotent-element-Monoid p n =
    compute-power-is-idempotent-element-Semigroup
      ( semigroup-Monoid M)
      ( p)
      ( nonzero-succ-ℕ n)

  compute-power-is-idempotent-element-Monoid :
    is-idempotent-element-Monoid M x →
    (n : ℕ) → is-nonzero-ℕ n → power-Monoid M n x ＝ x
  compute-power-is-idempotent-element-Monoid H zero-ℕ K =
    ex-falso (K refl)
  compute-power-is-idempotent-element-Monoid H (succ-ℕ n) K =
    compute-power-succ-is-idempotent-element-Monoid H n
```

### If `x` and `y` are idempotent and commute with each other, then `xy` is idempotent

```agda
module _
  {l1 : Level} (M : Monoid l1) {x y : type-Monoid M}
  where

  is-idempotent-element-mul-Monoid :
    mul-Monoid M x y ＝ mul-Monoid M y x →
    is-idempotent-element-Monoid M x →
    is-idempotent-element-Monoid M y →
    is-idempotent-element-Monoid M (mul-Monoid M x y)
  is-idempotent-element-mul-Monoid =
    is-idempotent-element-mul-Semigroup (semigroup-Monoid M)
```

