# The large additive group of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.large-additive-group-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.additive-group-of-rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.large-abelian-groups
open import group-theory.large-commutative-monoids
open import group-theory.large-groups
open import group-theory.large-monoids
open import group-theory.large-semigroups

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) form a
[large abelian group](group-theory.large-abelian-groups.md) under
[addition](real-numbers.addition-real-numbers.md).

## Definition

```agda
large-semigroup-add-ℝ : Large-Semigroup lsuc (_⊔_)
large-semigroup-add-ℝ =
  λ where
    .cumulative-large-set-Large-Semigroup →
      cumulative-large-set-ℝ
    .sim-preserving-binary-operator-mul-Large-Semigroup →
      sim-preserving-binary-operator-add-ℝ
    .associative-mul-Large-Semigroup →
      associative-add-ℝ

large-monoid-add-ℝ : Large-Monoid lsuc (_⊔_)
large-monoid-add-ℝ =
  λ where
    .large-semigroup-Large-Monoid →
      large-semigroup-add-ℝ
    .unit-Large-Monoid →
      zero-ℝ
    .left-unit-law-mul-Large-Monoid →
      left-unit-law-add-ℝ
    .right-unit-law-mul-Large-Monoid →
      right-unit-law-add-ℝ

large-commutative-monoid-add-ℝ : Large-Commutative-Monoid lsuc (_⊔_)
large-commutative-monoid-add-ℝ =
  make-Large-Commutative-Monoid
    ( large-monoid-add-ℝ)
    ( commutative-add-ℝ)

large-group-add-ℝ : Large-Group lsuc (_⊔_)
large-group-add-ℝ =
  λ where
    .large-monoid-Large-Group →
      large-monoid-add-ℝ
    .inv-Large-Group →
      neg-ℝ
    .sim-left-inverse-law-mul-Large-Group →
      left-inverse-law-add-ℝ
    .sim-right-inverse-law-mul-Large-Group →
      right-inverse-law-add-ℝ

large-ab-add-ℝ : Large-Ab lsuc (_⊔_)
large-ab-add-ℝ =
  make-Large-Ab
    ( large-group-add-ℝ)
    ( commutative-add-ℝ)
```

## Properties

### The small abelian group of real numbers at a universe level

```agda
ab-add-ℝ : (l : Level) → Ab (lsuc l)
ab-add-ℝ = ab-Large-Ab large-ab-add-ℝ
```

### The canonical embedding of rational numbers in the real numbers is an abelian group homomorphism

```agda
hom-ab-add-real-ℚ : hom-Ab abelian-group-add-ℚ (ab-add-ℝ lzero)
hom-ab-add-real-ℚ = (real-ℚ , inv (add-real-ℚ _ _))
```

### Raising the universe levels of real numbers is an abelian group homomorphism

```agda
hom-ab-add-raise-ℝ : (l1 l2 : Level) → hom-Ab (ab-add-ℝ l1) (ab-add-ℝ (l1 ⊔ l2))
hom-ab-add-raise-ℝ = hom-raise-Large-Ab large-ab-add-ℝ
```
