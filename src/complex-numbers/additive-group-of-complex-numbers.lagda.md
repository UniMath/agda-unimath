# The additive group of complex numbers

```agda
module complex-numbers.additive-group-of-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The type of [complex numbers](complex-numbers.complex-numbers.md) equipped with
[addition](complex-numbers.addition-complex-numbers.md) is a
[commutative group](group-theory.abelian-groups.md) with unit `zero-ℂ` and
inverse given by `neg-ℂ`.

## Definition

```agda
semigroup-add-ℂ-lzero : Semigroup (lsuc lzero)
semigroup-add-ℂ-lzero =
  ( ℂ-Set lzero ,
    add-ℂ ,
    associative-add-ℂ)

group-add-ℂ-lzero : Group (lsuc lzero)
group-add-ℂ-lzero =
  ( semigroup-add-ℂ-lzero ,
    ( zero-ℂ , left-unit-law-add-ℂ , right-unit-law-add-ℂ) ,
    neg-ℂ ,
    eq-sim-ℂ ∘ left-inverse-law-add-ℂ ,
    eq-sim-ℂ ∘ right-inverse-law-add-ℂ)

ab-add-ℂ-lzero : Ab (lsuc lzero)
ab-add-ℂ-lzero =
  ( group-add-ℂ-lzero ,
    commutative-add-ℂ)
```
