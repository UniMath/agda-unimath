# The commutative semiring of natural numbers

```agda
module elementary-number-theory.commutative-semiring-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.monoid-of-natural-numbers-with-addition
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-commutative-monoids

open import ring-theory.homomorphisms-semirings
open import ring-theory.semirings
```

</details>

## Definition

### The commutative semiring of natural numbers

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
  map-nat-Semiring n = mul-nat-scalar-Semiring R n (one-Semiring R)

  htpy-mul-map-mul-nat-scalar-Semiring :
    (n : ℕ) →
    mul-Semiring R (map-nat-Semiring n) ~
    mul-nat-scalar-Semiring R n
  htpy-mul-map-mul-nat-scalar-Semiring n x =
    ( left-nat-scalar-law-mul-Semiring R n (one-Semiring R) x) ∙
    ( ap (mul-nat-scalar-Semiring R n) (left-unit-law-mul-Semiring R x))

  preserves-add-map-nat-Semiring :
    (m n : ℕ) →
    map-nat-Semiring (m +ℕ n) ＝
    add-Semiring
      ( R)
      ( map-nat-Semiring m)
      ( map-nat-Semiring n)
  preserves-add-map-nat-Semiring m n =
    right-distributive-mul-nat-scalar-add-Semiring
      ( R)
      ( m)
      ( n)
      ( one-Semiring R)

  preserves-one-map-nat-Semiring :
    map-nat-Semiring 1 ＝ one-Semiring R
  preserves-one-map-nat-Semiring =
    left-unit-law-mul-nat-scalar-Semiring R (one-Semiring R)

  preserves-mul-map-nat-Semiring :
    (m n : ℕ) →
    map-nat-Semiring (m *ℕ n) ＝
    mul-Semiring
      ( R)
      ( map-nat-Semiring m)
      ( map-nat-Semiring n)
  preserves-mul-map-nat-Semiring m n =
    htpy-comp-mul-nat-mul-Semiring R m n (one-Semiring R) ∙
    inv (htpy-mul-map-mul-nat-scalar-Semiring m (map-nat-Semiring n))

module _
  {l : Level} (R : Semiring l)
  where

  initial-hom-Semiring : hom-Semiring ℕ-Semiring R
  pr1 (pr1 initial-hom-Semiring) =
    ( map-nat-Semiring R ,
      λ {m n} → preserves-add-map-nat-Semiring R m n)
  pr2 (pr1 initial-hom-Semiring) =
    left-zero-law-mul-nat-scalar-Semiring R (one-Semiring R)
  pr1 (pr2 initial-hom-Semiring) {m} {n} =
    preserves-mul-map-nat-Semiring R m n
  pr2 (pr2 initial-hom-Semiring) =
    preserves-one-map-nat-Semiring R
```
