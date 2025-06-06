# Finite sequences in rings

```agda
module linear-algebra.finite-sequences-in-rings where
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

open import linear-algebra.finite-sequences-in-semirings

open import lists.finite-sequences
open import lists.functoriality-finite-sequences

open import ring-theory.rings
```

</details>

## Idea

Given a [ring](ring-theory.rings.md) `R`, the type `fin-sequence n R` of
[finite sequences](lists.finite-sequences.md) in the underlying type of `R` of
length `n` is an [abelian group](group-theory.abelian-groups.md).

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where

  fin-sequence-type-Ring : ℕ → UU l
  fin-sequence-type-Ring = fin-sequence (type-Ring R)

  head-fin-sequence-type-Ring :
    (n : ℕ) → fin-sequence-type-Ring (succ-ℕ n) → type-Ring R
  head-fin-sequence-type-Ring n v = head-fin-sequence n v

  tail-fin-sequence-type-Ring :
    (n : ℕ) → fin-sequence-type-Ring (succ-ℕ n) → fin-sequence-type-Ring n
  tail-fin-sequence-type-Ring = tail-fin-sequence

  cons-fin-sequence-type-Ring :
    (n : ℕ) → type-Ring R →
    fin-sequence-type-Ring n → fin-sequence-type-Ring (succ-ℕ n)
  cons-fin-sequence-type-Ring = cons-fin-sequence

  snoc-fin-sequence-type-Ring :
    (n : ℕ) → fin-sequence-type-Ring n → type-Ring R →
    fin-sequence-type-Ring (succ-ℕ n)
  snoc-fin-sequence-type-Ring = snoc-fin-sequence
```

### The zero finite sequence in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-fin-sequence-type-Ring : (n : ℕ) → fin-sequence-type-Ring R n
  zero-fin-sequence-type-Ring n i = zero-Ring R
```

### Pointwise addition of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-fin-sequence-type-Ring :
    (n : ℕ) (v w : fin-sequence-type-Ring R n) → fin-sequence-type-Ring R n
  add-fin-sequence-type-Ring n = binary-map-fin-sequence n (add-Ring R)
```

### Pointwise negation of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) → fin-sequence-type-Ring R n
  neg-fin-sequence-type-Ring n = map-fin-sequence n (neg-Ring R)
```

## Properties of pointwise addition

### Associativity

```agda
module _
  {l : Level} (R : Ring l)
  where

  associative-add-fin-sequence-type-Ring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Ring R n) →
    ( add-fin-sequence-type-Ring R n
      ( add-fin-sequence-type-Ring R n v1 v2)
      ( v3)) ＝
    ( add-fin-sequence-type-Ring R n v1 (add-fin-sequence-type-Ring R n v2 v3))
  associative-add-fin-sequence-type-Ring =
    associative-add-fin-sequence-type-Semiring (semiring-Ring R)
```

### Unit laws

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-unit-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n (zero-fin-sequence-type-Ring R n) v ＝ v
  left-unit-law-add-fin-sequence-type-Ring =
    left-unit-law-add-fin-sequence-type-Semiring (semiring-Ring R)

  right-unit-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n v (zero-fin-sequence-type-Ring R n) ＝ v
  right-unit-law-add-fin-sequence-type-Ring =
    right-unit-law-add-fin-sequence-type-Semiring (semiring-Ring R)
```

### Commutativity

```agda
module _
  {l : Level} (R : Ring l)
  where

  commutative-add-fin-sequence-type-Ring :
    (n : ℕ) (v w : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n v w ＝ add-fin-sequence-type-Ring R n w v
  commutative-add-fin-sequence-type-Ring =
    commutative-add-fin-sequence-type-Semiring (semiring-Ring R)
```

### Inverse laws

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-inverse-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n (neg-fin-sequence-type-Ring R n v) v ＝
    zero-fin-sequence-type-Ring R n
  left-inverse-law-add-fin-sequence-type-Ring n v =
    eq-htpy (λ i → left-inverse-law-add-Ring R _)

  right-inverse-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n v (neg-fin-sequence-type-Ring R n v) ＝
    zero-fin-sequence-type-Ring R n
  right-inverse-law-add-fin-sequence-type-Ring n v =
    eq-htpy (λ i → right-inverse-law-add-Ring R _)
```

### The abelian group of pointwise addition

```agda
module _
  {l : Level} (R : Ring l)
  where

  semigroup-fin-sequence-type-Ring : ℕ → Semigroup l
  semigroup-fin-sequence-type-Ring =
    semigroup-fin-sequence-type-Semiring (semiring-Ring R)

  monoid-fin-sequence-type-Ring : ℕ → Monoid l
  monoid-fin-sequence-type-Ring =
    monoid-fin-sequence-type-Semiring (semiring-Ring R)

  commutative-monoid-fin-sequence-type-Ring : ℕ → Commutative-Monoid l
  commutative-monoid-fin-sequence-type-Ring =
    commutative-monoid-fin-sequence-type-Semiring (semiring-Ring R)

  is-unital-fin-sequence-type-Ring :
    (n : ℕ) → is-unital (add-fin-sequence-type-Ring R n)
  is-unital-fin-sequence-type-Ring n =
    is-unital-Monoid (monoid-fin-sequence-type-Ring n)

  is-group-fin-sequence-type-Ring :
    (n : ℕ) → is-group-Semigroup (semigroup-fin-sequence-type-Ring n)
  pr1 (is-group-fin-sequence-type-Ring n) = is-unital-fin-sequence-type-Ring n
  pr1 (pr2 (is-group-fin-sequence-type-Ring n)) = neg-fin-sequence-type-Ring R n
  pr1 (pr2 (pr2 (is-group-fin-sequence-type-Ring n))) =
    left-inverse-law-add-fin-sequence-type-Ring R n
  pr2 (pr2 (pr2 (is-group-fin-sequence-type-Ring n))) =
    right-inverse-law-add-fin-sequence-type-Ring R n

  group-fin-sequence-type-Ring : ℕ → Group l
  pr1 (group-fin-sequence-type-Ring n) = semigroup-fin-sequence-type-Ring n
  pr2 (group-fin-sequence-type-Ring n) = is-group-fin-sequence-type-Ring n

  ab-fin-sequence-type-Ring : ℕ → Ab l
  pr1 (ab-fin-sequence-type-Ring n) = group-fin-sequence-type-Ring n
  pr2 (ab-fin-sequence-type-Ring n) = commutative-add-fin-sequence-type-Ring R n
```
