# Idempotent elements of semigroups

```agda
module group-theory.idempotent-elements-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions

open import group-theory.powers-of-elements-semigroups
open import group-theory.semigroups
```

</details>

## Idea

An element `x` of a [semigroup](group-theory.semigroups.md) is said to be
{{#concept "idempotent" Disambiguation="element of a semigroup" Agda=is-idempotent-element-Semigroup}} if it satisfies the [identity](foundation-core.identity-types.md)

```text
  xx ＝ x.
```

## Definitions

### The predicate of being an idempotent element

```agda
module _
  {l1 : Level} (G : Semigroup l1) (x : type-Semigroup G)
  where

  is-idempotent-element-Semigroup : UU l1
  is-idempotent-element-Semigroup = mul-Semigroup G x x ＝ x

  is-prop-is-idempotent-element-Semigroup :
    is-prop is-idempotent-element-Semigroup
  is-prop-is-idempotent-element-Semigroup =
    is-set-type-Semigroup G _ _

  is-idempotent-element-prop-Semigroup :
    Prop l1
  pr1 is-idempotent-element-prop-Semigroup =
    is-idempotent-element-Semigroup
  pr2 is-idempotent-element-prop-Semigroup =
    is-prop-is-idempotent-element-Semigroup
```

## Properties

### If `x` is idempotent, then `xⁿ ＝ x` for all `n ≥ 1`

```agda
module _
  {l1 : Level} (G : Semigroup l1) {x : type-Semigroup G}
  where

  compute-power-succ-is-idempotent-element-Semigroup :
    is-idempotent-element-Semigroup G x →
    (n : ℕ) → power-succ-Semigroup G n x ＝ x
  compute-power-succ-is-idempotent-element-Semigroup p zero-ℕ = refl
  compute-power-succ-is-idempotent-element-Semigroup p (succ-ℕ n) =
    ap
      ( mul-Semigroup' G _)
      ( compute-power-succ-is-idempotent-element-Semigroup p n) ∙
    p

  compute-power-is-idempotent-element-Semigroup :
    is-idempotent-element-Semigroup G x →
    (n : ℕ⁺) → power-Semigroup G n x ＝ x
  compute-power-is-idempotent-element-Semigroup H (zero-ℕ , K) =
    ex-falso (K refl)
  compute-power-is-idempotent-element-Semigroup H (succ-ℕ n , K) =
    compute-power-succ-is-idempotent-element-Semigroup H n
```

### If `x` and `y` are idempotent and commute with each other, then `xy` is idempotent

```agda
module _
  {l1 : Level} (G : Semigroup l1) {x y : type-Semigroup G}
  where

  is-idempotent-element-mul-Semigroup :
    mul-Semigroup G x y ＝ mul-Semigroup G y x →
    is-idempotent-element-Semigroup G x →
    is-idempotent-element-Semigroup G y →
    is-idempotent-element-Semigroup G (mul-Semigroup G x y)
  is-idempotent-element-mul-Semigroup p H K =
    interchange-mul-mul-Semigroup G (inv p) ∙ ap-mul-Semigroup G H K
```
