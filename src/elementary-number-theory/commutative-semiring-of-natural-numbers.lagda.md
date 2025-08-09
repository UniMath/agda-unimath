# The commutative semiring of natural numbers

```agda
module elementary-number-theory.commutative-semiring-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.homomorphisms-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.monoid-of-natural-numbers-with-addition
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.powers-of-elements-commutative-monoids

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

### The semiring of natural numbers is the initial semiring

#### The homomorphism from `ℕ` to a semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  map-initial-hom-Semiring : ℕ → type-Semiring R
  map-initial-hom-Semiring zero-ℕ = zero-Semiring R
  map-initial-hom-Semiring (succ-ℕ n) =
    add-Semiring R (map-initial-hom-Semiring n) (one-Semiring R)

  preserves-add-initial-hom-Semiring :
    (m n : ℕ) →
    map-initial-hom-Semiring (m +ℕ n) ＝
    add-Semiring R (map-initial-hom-Semiring m) (map-initial-hom-Semiring n)
  preserves-add-initial-hom-Semiring m zero-ℕ =
    inv (right-unit-law-add-Semiring R _)
  preserves-add-initial-hom-Semiring m (succ-ℕ n) =
    ap-add-Semiring R (preserves-add-initial-hom-Semiring m n) refl ∙
    associative-add-Semiring R _ _ _

  preserves-one-initial-hom-Semiring :
    map-initial-hom-Semiring 1 ＝ one-Semiring R
  preserves-one-initial-hom-Semiring = left-unit-law-add-Semiring R _

  preserves-mul-initial-hom-Semiring :
    (m n : ℕ) →
    map-initial-hom-Semiring (m *ℕ n) ＝
    mul-Semiring R (map-initial-hom-Semiring m) (map-initial-hom-Semiring n)
  preserves-mul-initial-hom-Semiring zero-ℕ n =
    inv (left-zero-law-mul-Semiring R _)
  preserves-mul-initial-hom-Semiring (succ-ℕ m) n =
    equational-reasoning
      map-initial-hom-Semiring (succ-ℕ m *ℕ n)
      ＝
        add-Semiring R
          ( map-initial-hom-Semiring (m *ℕ n))
          ( map-initial-hom-Semiring n)
        by preserves-add-initial-hom-Semiring (m *ℕ n) n
      ＝
        add-Semiring R
          ( mul-Semiring R
            ( map-initial-hom-Semiring m)
            ( map-initial-hom-Semiring n))
          ( mul-Semiring R (one-Semiring R) (map-initial-hom-Semiring n))
        by
          ap-add-Semiring R
            ( preserves-mul-initial-hom-Semiring m n)
            ( inv (left-unit-law-mul-Semiring R _))
      ＝
        mul-Semiring R
          ( map-initial-hom-Semiring (succ-ℕ m))
          ( map-initial-hom-Semiring n)
        by inv (right-distributive-mul-add-Semiring R _ _ _)

  initial-hom-Semiring : hom-Semiring ℕ-Semiring R
  initial-hom-Semiring =
    ( ( ( map-initial-hom-Semiring ,
          λ {m} {n} → preserves-add-initial-hom-Semiring m n) ,
        refl) ,
      ( λ {m} {n} → preserves-mul-initial-hom-Semiring m n) ,
      preserves-one-initial-hom-Semiring)
```

#### Multiplying by the image of n is adding n times

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    left-mul-initial-hom-Semiring :
      (n : ℕ) (x : type-Semiring R) →
      mul-Semiring R
        ( map-initial-hom-Semiring R n)
        ( x) ＝
      power-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( n)
        ( x)
    left-mul-initial-hom-Semiring 0 x = left-zero-law-mul-Semiring R x
    left-mul-initial-hom-Semiring 1 x =
      ap-mul-Semiring R (preserves-one-initial-hom-Semiring R) refl ∙
      left-unit-law-mul-Semiring R x
    left-mul-initial-hom-Semiring (succ-ℕ (succ-ℕ n)) x =
      right-distributive-mul-add-Semiring R _ _ _ ∙
      ap-add-Semiring R
        ( left-mul-initial-hom-Semiring (succ-ℕ n) x)
        ( left-unit-law-mul-Semiring R x)
```

### The commutative semiring of integers is the initial commutative semiring

#### The homomorphism from `ℕ` to a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  map-initial-hom-Commutative-Semiring : ℕ → type-Commutative-Semiring R
  map-initial-hom-Commutative-Semiring =
    map-initial-hom-Semiring (semiring-Commutative-Semiring R)

  initial-hom-Commutative-Semiring :
    hom-Commutative-Semiring ℕ-Commutative-Semiring R
  initial-hom-Commutative-Semiring =
    initial-hom-Semiring (semiring-Commutative-Semiring R)
```

#### Multiplying by the image of n is adding n times

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  abstract
    left-mul-initial-hom-Commutative-Semiring :
      (n : ℕ) (x : type-Commutative-Semiring R) →
      mul-Commutative-Semiring R
        ( map-initial-hom-Commutative-Semiring R n)
        ( x) ＝
      power-Commutative-Monoid
        ( additive-commutative-monoid-Commutative-Semiring R)
        ( n)
        ( x)
    left-mul-initial-hom-Commutative-Semiring =
      left-mul-initial-hom-Semiring (semiring-Commutative-Semiring R)
```
