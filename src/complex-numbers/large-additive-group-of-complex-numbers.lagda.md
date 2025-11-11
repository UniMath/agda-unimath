# The large additive group of complex numbers

```agda
module complex-numbers.large-additive-group-of-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.large-abelian-groups
open import group-theory.large-commutative-monoids
open import group-theory.large-groups
open import group-theory.large-monoids
open import group-theory.large-semigroups
```

</details>

## Idea

The type of [complex numbers](complex-numbers.complex-numbers.md) equipped with
[addition](complex-numbers.addition-complex-numbers.md) is a
[large abelian group](group-theory.large-abelian-groups.md).

## Definition

```agda
large-semigroup-add-ℂ : Large-Semigroup lsuc
large-semigroup-add-ℂ =
  make-Large-Semigroup
    ( ℂ-Set)
    ( add-ℂ)
    ( associative-add-ℂ)

large-monoid-add-ℂ : Large-Monoid lsuc (_⊔_)
large-monoid-add-ℂ =
  make-Large-Monoid
    ( large-semigroup-add-ℂ)
    ( large-similarity-relation-ℂ)
    ( raise-ℂ)
    ( sim-raise-ℂ)
    ( λ _ _ z~z' _ _ → preserves-sim-add-ℂ z~z')
    ( zero-ℂ)
    ( left-unit-law-add-ℂ)
    ( right-unit-law-add-ℂ)

large-commutative-monoid-add-ℂ : Large-Commutative-Monoid lsuc (_⊔_)
large-commutative-monoid-add-ℂ =
  make-Large-Commutative-Monoid
    ( large-monoid-add-ℂ)
    ( commutative-add-ℂ)

large-group-add-ℂ : Large-Group lsuc (_⊔_)
large-group-add-ℂ =
  make-Large-Group
    ( large-monoid-add-ℂ)
    ( neg-ℂ)
    ( λ _ _ → preserves-sim-neg-ℂ)
    ( λ x →
      eq-sim-ℂ
        ( transitive-sim-ℂ
          ( neg-ℂ x +ℂ x)
          ( zero-ℂ)
          ( raise-ℂ _ zero-ℂ)
          ( sim-raise-ℂ _ zero-ℂ)
          ( left-inverse-law-add-ℂ x)))
    ( λ x →
      eq-sim-ℂ
        ( transitive-sim-ℂ
          ( x +ℂ neg-ℂ x)
          ( zero-ℂ)
          ( raise-ℂ _ zero-ℂ)
          ( sim-raise-ℂ _ zero-ℂ)
          ( right-inverse-law-add-ℂ x)))

large-ab-add-ℂ : Large-Ab lsuc (_⊔_)
large-ab-add-ℂ =
  make-Large-Ab
    ( large-group-add-ℂ)
    ( commutative-add-ℂ)
```

## Properties

### The small abelian group of complex numbers at a universe level

```agda
ab-add-ℂ : (l : Level) → Ab (lsuc l)
ab-add-ℂ = ab-Large-Ab large-ab-add-ℂ
```
