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
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.large-abelian-groups
open import group-theory.large-commutative-monoids
open import group-theory.large-groups
open import group-theory.large-monoids
open import group-theory.large-semigroups

open import real-numbers.large-additive-group-of-real-numbers
```

</details>

## Idea

The type of [complex numbers](complex-numbers.complex-numbers.md) equipped with
[addition](complex-numbers.addition-complex-numbers.md) is a
[large abelian group](group-theory.large-abelian-groups.md).

## Definition

```agda
large-semigroup-add-ℂ : Large-Semigroup lsuc (_⊔_)
large-semigroup-add-ℂ =
  λ where
    .cumulative-large-set-Large-Semigroup →
      cumulative-large-set-ℂ
    .sim-preserving-binary-operator-mul-Large-Semigroup →
      sim-preserving-binary-operator-add-ℂ
    .associative-mul-Large-Semigroup →
      associative-add-ℂ

large-monoid-add-ℂ : Large-Monoid lsuc (_⊔_)
large-monoid-add-ℂ =
  λ where
    .large-semigroup-Large-Monoid →
      large-semigroup-add-ℂ
    .unit-Large-Monoid →
      zero-ℂ
    .left-unit-law-mul-Large-Monoid →
      left-unit-law-add-ℂ
    .right-unit-law-mul-Large-Monoid →
      right-unit-law-add-ℂ

large-commutative-monoid-add-ℂ : Large-Commutative-Monoid lsuc (_⊔_)
large-commutative-monoid-add-ℂ =
  make-Large-Commutative-Monoid
    ( large-monoid-add-ℂ)
    ( commutative-add-ℂ)

large-group-add-ℂ : Large-Group lsuc (_⊔_)
large-group-add-ℂ =
  λ where
    .large-monoid-Large-Group →
      large-monoid-add-ℂ
    .inv-Large-Group →
      neg-ℂ
    .sim-left-inverse-law-mul-Large-Group →
      left-inverse-law-add-ℂ
    .sim-right-inverse-law-mul-Large-Group →
      right-inverse-law-add-ℂ

large-ab-add-ℂ : Large-Ab lsuc (_⊔_)
large-ab-add-ℂ =
  make-Large-Ab
    ( large-group-add-ℂ)
    ( commutative-add-ℂ)
```

## Properties

### The abelian group of complex numbers at a universe level

```agda
ab-add-ℂ : (l : Level) → Ab (lsuc l)
ab-add-ℂ = ab-Large-Ab large-ab-add-ℂ
```

### The canonical abelian group homomorphism from the additive group of `ℝ` to the additive group of `ℂ`

```agda
hom-add-ab-complex-ℝ : (l : Level) → hom-Ab (ab-add-ℝ l) (ab-add-ℂ l)
hom-add-ab-complex-ℝ l = (complex-ℝ , inv (add-complex-ℝ _ _))
```
