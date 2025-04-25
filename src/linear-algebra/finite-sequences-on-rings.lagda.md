# Finite sequences on rings

```agda
module linear-algebra.finite-sequences-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.finite-sequences
open import linear-algebra.finite-sequences-on-semirings
open import linear-algebra.functoriality-finite-sequences

open import ring-theory.rings
```

</details>

## Idea

Given a [ring](ring-theory.rings.md) `R`, the type `fin-sequence n R` of
`R`-[finite sequences](linear-algebra.finite-sequences.md) is an
[Abelian group](group-theory.abelian-groups.md).

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where

  fin-sequence-Ring : ℕ → UU l
  fin-sequence-Ring = fin-sequence (type-Ring R)

  head-fin-sequence-Ring :
    (n : ℕ) → fin-sequence-Ring (succ-ℕ n) → type-Ring R
  head-fin-sequence-Ring n v = head-fin-sequence n v

  tail-fin-sequence-Ring :
    (n : ℕ) → fin-sequence-Ring (succ-ℕ n) → fin-sequence-Ring n
  tail-fin-sequence-Ring = tail-fin-sequence

  cons-fin-sequence-Ring :
    (n : ℕ) → type-Ring R →
    fin-sequence-Ring n → fin-sequence-Ring (succ-ℕ n)
  cons-fin-sequence-Ring = cons-fin-sequence

  snoc-fin-sequence-Ring :
    (n : ℕ) → fin-sequence-Ring n → type-Ring R →
    fin-sequence-Ring (succ-ℕ n)
  snoc-fin-sequence-Ring = snoc-fin-sequence
```

### Zero finite sequence on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-fin-sequence-Ring : (n : ℕ) → fin-sequence-Ring R n
  zero-fin-sequence-Ring n i = zero-Ring R
```

### Pointwise addition of finite sequences on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-fin-sequence-Ring :
    (n : ℕ) (v w : fin-sequence-Ring R n) → fin-sequence-Ring R n
  add-fin-sequence-Ring n = binary-map-fin-sequence n (add-Ring R)
```

### Pointwise negation of finite sequences on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-fin-sequence-Ring :
    (n : ℕ) (v : fin-sequence-Ring R n) → fin-sequence-Ring R n
  neg-fin-sequence-Ring n = map-fin-sequence n (neg-Ring R)
```

## Properties of pointwise addition

### Associativity

```agda
module _
  {l : Level} (R : Ring l)
  where

  associative-add-fin-sequence-Ring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-Ring R n) →
    ( add-fin-sequence-Ring R n (add-fin-sequence-Ring R n v1 v2) v3) ＝
    ( add-fin-sequence-Ring R n v1 (add-fin-sequence-Ring R n v2 v3))
  associative-add-fin-sequence-Ring =
    associative-add-fin-sequence-Semiring (semiring-Ring R)
```

### Unit laws

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-unit-law-add-fin-sequence-Ring :
    (n : ℕ) (v : fin-sequence-Ring R n) →
    add-fin-sequence-Ring R n (zero-fin-sequence-Ring R n) v ＝ v
  left-unit-law-add-fin-sequence-Ring =
    left-unit-law-add-fin-sequence-Semiring (semiring-Ring R)

  right-unit-law-add-fin-sequence-Ring :
    (n : ℕ) (v : fin-sequence-Ring R n) →
    add-fin-sequence-Ring R n v (zero-fin-sequence-Ring R n) ＝ v
  right-unit-law-add-fin-sequence-Ring =
    right-unit-law-add-fin-sequence-Semiring (semiring-Ring R)
```

### Commutativity

```agda
module _
  {l : Level} (R : Ring l)
  where

  commutative-add-fin-sequence-Ring :
    (n : ℕ) (v w : fin-sequence-Ring R n) →
    add-fin-sequence-Ring R n v w ＝ add-fin-sequence-Ring R n w v
  commutative-add-fin-sequence-Ring =
    commutative-add-fin-sequence-Semiring (semiring-Ring R)
```

### Inverse laws

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-inverse-law-add-fin-sequence-Ring :
    (n : ℕ) (v : fin-sequence-Ring R n) →
    add-fin-sequence-Ring R n (neg-fin-sequence-Ring R n v) v ＝
    zero-fin-sequence-Ring R n
  left-inverse-law-add-fin-sequence-Ring n v =
    eq-htpy (λ i → left-inverse-law-add-Ring R _)

  right-inverse-law-add-fin-sequence-Ring :
    (n : ℕ) (v : fin-sequence-Ring R n) →
    add-fin-sequence-Ring R n v (neg-fin-sequence-Ring R n v) ＝
    zero-fin-sequence-Ring R n
  right-inverse-law-add-fin-sequence-Ring n v =
    eq-htpy (λ i → right-inverse-law-add-Ring R _)
```

### Abelian group of pointwise addition

```agda
module _
  {l : Level} (R : Ring l)
  where

  fin-sequence-Ring-Semigroup : ℕ → Semigroup l
  fin-sequence-Ring-Semigroup =
    fin-sequence-Semiring-Semigroup (semiring-Ring R)

  fin-sequence-Ring-Monoid : ℕ → Monoid l
  fin-sequence-Ring-Monoid =
    fin-sequence-Semiring-Monoid (semiring-Ring R)

  fin-sequence-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  fin-sequence-Ring-Commutative-Monoid =
    fin-sequence-Semiring-Commutative-Monoid (semiring-Ring R)

  is-unital-fin-sequence-Ring :
    (n : ℕ) → is-unital (add-fin-sequence-Ring R n)
  is-unital-fin-sequence-Ring n = is-unital-Monoid (fin-sequence-Ring-Monoid n)

  is-group-fin-sequence-Ring :
    (n : ℕ) → is-group-Semigroup (fin-sequence-Ring-Semigroup n)
  pr1 (is-group-fin-sequence-Ring n) = is-unital-fin-sequence-Ring n
  pr1 (pr2 (is-group-fin-sequence-Ring n)) = neg-fin-sequence-Ring R n
  pr1 (pr2 (pr2 (is-group-fin-sequence-Ring n))) =
    left-inverse-law-add-fin-sequence-Ring R n
  pr2 (pr2 (pr2 (is-group-fin-sequence-Ring n))) =
    right-inverse-law-add-fin-sequence-Ring R n

  fin-sequence-Ring-Group : ℕ → Group l
  pr1 (fin-sequence-Ring-Group n) = fin-sequence-Ring-Semigroup n
  pr2 (fin-sequence-Ring-Group n) = is-group-fin-sequence-Ring n

  fin-sequence-Ring-Ab : ℕ → Ab l
  pr1 (fin-sequence-Ring-Ab n) = fin-sequence-Ring-Group n
  pr2 (fin-sequence-Ring-Ab n) = commutative-add-fin-sequence-Ring R n
```
