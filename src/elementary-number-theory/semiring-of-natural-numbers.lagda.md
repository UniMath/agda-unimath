# The semiring of natural numbers

```agda
module elementary-number-theory.semiring-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.monoid-of-natural-numbers-with-addition
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-commutative-monoids

open import ring-theory.homomorphisms-semirings
open import ring-theory.multiples-of-elements-semirings
open import ring-theory.semirings
```

</details>

## Idea

The type of [natural numbers](elementary-number-theory.natural-numbers.md)
equipped with [addition](elementary-number-theory.addition-natural-numbers.md)
and [multiplication](elementary-number-theory.multiplication-natural-numbers.md)
is a [commutative semiring](commutative-algebra.commutative-semirings.md).

The {{#concept "semiring of natural numbers" Agda=ℕ-Semiring}} is the
**initial** semiring: for any semiring `R`, there's a unique
[semiring homomorphism](ring-theory.homomorphisms-semirings.md) from `ℕ` to `R`,
i.e., the type of semiring homomorphisms `hom-Semiring ℕ-Semiring R` is
[contractible](foundation.contractible-types.md).

## Definition

### The semiring of natural numbers

```agda
has-mul-ℕ-Commutative-Monoid :
  has-mul-Commutative-Monoid ℕ-Commutative-Monoid
pr1 (pr1 has-mul-ℕ-Commutative-Monoid) = mul-ℕ
pr2 (pr1 has-mul-ℕ-Commutative-Monoid) = associative-mul-ℕ
pr1 (pr1 (pr2 has-mul-ℕ-Commutative-Monoid)) = 1
pr1 (pr2 (pr1 (pr2 has-mul-ℕ-Commutative-Monoid))) = left-unit-law-mul-ℕ
pr2 (pr2 (pr1 (pr2 has-mul-ℕ-Commutative-Monoid))) = right-unit-law-mul-ℕ
pr1 (pr2 (pr2 has-mul-ℕ-Commutative-Monoid)) = left-distributive-mul-add-ℕ
pr2 (pr2 (pr2 has-mul-ℕ-Commutative-Monoid)) = right-distributive-mul-add-ℕ

ℕ-Semiring : Semiring lzero
pr1 ℕ-Semiring = ℕ-Commutative-Monoid
pr1 (pr2 ℕ-Semiring) = has-mul-ℕ-Commutative-Monoid
pr1 (pr2 (pr2 ℕ-Semiring)) = left-zero-law-mul-ℕ
pr2 (pr2 (pr2 ℕ-Semiring)) = right-zero-law-mul-ℕ
```

### The commutative semiring of natural numbers

```agda
ℕ-Commutative-Semiring : Commutative-Semiring lzero
pr1 ℕ-Commutative-Semiring = ℕ-Semiring
pr2 ℕ-Commutative-Semiring = commutative-mul-ℕ
```

### The initial inclusion of the natural numbers in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  map-nat-Semiring : ℕ → type-Semiring R
  map-nat-Semiring n = multiple-Semiring R n (one-Semiring R)

  htpy-mul-map-multiple-Semiring :
    (n : ℕ) →
    mul-Semiring R (map-nat-Semiring n) ~
    multiple-Semiring R n
  htpy-mul-map-multiple-Semiring n x =
    ( left-mul-multiple-Semiring R n (one-Semiring R) x) ∙
    ( ap (multiple-Semiring R n) (left-unit-law-mul-Semiring R x))

  preserves-add-map-nat-Semiring :
    (m n : ℕ) →
    map-nat-Semiring (m +ℕ n) ＝
    add-Semiring
      ( R)
      ( map-nat-Semiring m)
      ( map-nat-Semiring n)
  preserves-add-map-nat-Semiring m n =
    right-distributive-multiple-add-Semiring
      ( R)
      ( m)
      ( n)
      ( one-Semiring R)

  preserves-one-map-nat-Semiring :
    map-nat-Semiring 1 ＝ one-Semiring R
  preserves-one-map-nat-Semiring =
    left-unit-law-multiple-Semiring R (one-Semiring R)

  preserves-mul-map-nat-Semiring :
    (m n : ℕ) →
    map-nat-Semiring (m *ℕ n) ＝
    mul-Semiring
      ( R)
      ( map-nat-Semiring m)
      ( map-nat-Semiring n)
  preserves-mul-map-nat-Semiring m n =
    htpy-comp-mul-nat-mul-Semiring R m n (one-Semiring R) ∙
    inv (htpy-mul-map-multiple-Semiring m (map-nat-Semiring n))

module _
  {l : Level} (R : Semiring l)
  where

  initial-hom-Semiring : hom-Semiring ℕ-Semiring R
  pr1 (pr1 initial-hom-Semiring) =
    ( map-nat-Semiring R ,
      λ {m n} → preserves-add-map-nat-Semiring R m n)
  pr2 (pr1 initial-hom-Semiring) =
    left-zero-law-multiple-Semiring R (one-Semiring R)
  pr1 (pr2 initial-hom-Semiring) {m} {n} =
    preserves-mul-map-nat-Semiring R m n
  pr2 (pr2 initial-hom-Semiring) =
    preserves-one-map-nat-Semiring R
```

### Any semiring homomorphism from `ℕ` to a semiring is the initial inclusion

```agda
module _
  {l : Level} (R : Semiring l) (f : hom-Semiring ℕ-Semiring R)
  where

  htpy-map-nat-hom-Semiring :
    map-nat-Semiring R ~ map-hom-Semiring ℕ-Semiring R f
  htpy-map-nat-hom-Semiring 0 =
    inv (preserves-zero-hom-Semiring ℕ-Semiring R f)
  htpy-map-nat-hom-Semiring (succ-ℕ n) =
    equational-reasoning
      multiple-Semiring R (succ-ℕ n) (one-Semiring R)
      ＝
        add-Semiring R
          ( multiple-Semiring R n (one-Semiring R))
          ( one-Semiring R)
        by
          multiple-succ-Semiring R n (one-Semiring R)
      ＝
        add-Semiring R
          ( map-hom-Semiring ℕ-Semiring R f n)
          ( map-hom-Semiring ℕ-Semiring R f 1)
        by
          ap-add-Semiring R
            ( htpy-map-nat-hom-Semiring n)
            ( inv (preserves-unit-hom-Semiring ℕ-Semiring R f))
      ＝ map-hom-Semiring ℕ-Semiring R f (succ-ℕ n)
        by inv (preserves-addition-hom-Semiring ℕ-Semiring R f)
```

### The type of semiring homomorphisms from `ℕ` to a semiring is contractible

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-initial-semiring-ℕ : is-contr (hom-Semiring ℕ-Semiring R)
  pr1 is-initial-semiring-ℕ = initial-hom-Semiring R
  pr2 is-initial-semiring-ℕ f =
    eq-htpy-hom-Semiring
      ( ℕ-Semiring)
      ( R)
      ( initial-hom-Semiring R)
      ( f)
      ( htpy-map-nat-hom-Semiring R f)
```
