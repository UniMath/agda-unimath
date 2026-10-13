# Real algebras

```agda
module linear-algebra.real-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.real-vector-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.large-ring-of-real-numbers
```

</details>

## Idea

A {{#concept "real algebra" Agda=ℝ-Algebra}} is an
[algebra](commutative-algebra.algebras-commutative-rings.md) over the
[commutative ring](real-numbers.large-ring-of-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
ℝ-Algebra : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
ℝ-Algebra l1 l2 = algebra-Commutative-Ring l2 (commutative-ring-ℝ l1)

module _
  {l1 l2 : Level}
  (A : ℝ-Algebra l1 l2)
  (let R = commutative-ring-ℝ l1)
  where

  vector-space-ℝ-Algebra : ℝ-Vector-Space l1 l2
  vector-space-ℝ-Algebra = left-module-algebra-Commutative-Ring R A

  ab-ℝ-Algebra : Ab l2
  ab-ℝ-Algebra = ab-ℝ-Vector-Space vector-space-ℝ-Algebra

  type-ℝ-Algebra : UU l2
  type-ℝ-Algebra = type-algebra-Commutative-Ring R A
```

## Properties

### Properties inherited from abelian group structure

```agda
module _
  {l1 l2 : Level}
  (A : ℝ-Algebra l1 l2)
  (let ab-A = ab-ℝ-Algebra A)
  where

  add-ℝ-Algebra : type-ℝ-Algebra A → type-ℝ-Algebra A → type-ℝ-Algebra A
  add-ℝ-Algebra = add-Ab ab-A

  neg-ℝ-Algebra : type-ℝ-Algebra A → type-ℝ-Algebra A
  neg-ℝ-Algebra = neg-Ab ab-A

  zero-ℝ-Algebra : type-ℝ-Algebra A
  zero-ℝ-Algebra = zero-Ab ab-A

  diff-ℝ-Algebra : type-ℝ-Algebra A → type-ℝ-Algebra A → type-ℝ-Algebra A
  diff-ℝ-Algebra = right-subtraction-Ab ab-A
```

### Properties inherited from vector space structure

```agda
module _
  {l1 l2 : Level}
  (A : ℝ-Algebra l1 l2)
  (let vs-A = vector-space-ℝ-Algebra A)
  where

  scalar-mul-ℝ-Algebra : ℝ l1 → type-ℝ-Algebra A → type-ℝ-Algebra A
  scalar-mul-ℝ-Algebra = mul-ℝ-Vector-Space vs-A
```

### Properties specific to algebras

```agda
module _
  {l1 l2 : Level}
  (A : ℝ-Algebra l1 l2)
  (let R = commutative-ring-ℝ l1)
  where

  mul-ℝ-Algebra : type-ℝ-Algebra A → type-ℝ-Algebra A → type-ℝ-Algebra A
  mul-ℝ-Algebra = mul-algebra-Commutative-Ring R A

  abstract
    left-distributive-mul-add-ℝ-Algebra :
      (x y z : type-ℝ-Algebra A) →
      mul-ℝ-Algebra x (add-ℝ-Algebra A y z) ＝
      add-ℝ-Algebra A (mul-ℝ-Algebra x y) (mul-ℝ-Algebra x z)
    left-distributive-mul-add-ℝ-Algebra =
      left-distributive-mul-add-algebra-Commutative-Ring R A

    left-distributive-mul-diff-ℝ-Algebra :
      (x y z : type-ℝ-Algebra A) →
      mul-ℝ-Algebra x (diff-ℝ-Algebra A y z) ＝
      diff-ℝ-Algebra A (mul-ℝ-Algebra x y) (mul-ℝ-Algebra x z)
    left-distributive-mul-diff-ℝ-Algebra =
      left-distributive-mul-diff-algebra-Commutative-Ring R A

    right-distributive-mul-add-ℝ-Algebra :
      (x y z : type-ℝ-Algebra A) →
      mul-ℝ-Algebra (add-ℝ-Algebra A x y) z ＝
      add-ℝ-Algebra A (mul-ℝ-Algebra x z) (mul-ℝ-Algebra y z)
    right-distributive-mul-add-ℝ-Algebra =
      right-distributive-mul-add-algebra-Commutative-Ring R A

    right-distributive-mul-diff-ℝ-Algebra :
      (x y z : type-ℝ-Algebra A) →
      mul-ℝ-Algebra (diff-ℝ-Algebra A x y) z ＝
      diff-ℝ-Algebra A (mul-ℝ-Algebra x z) (mul-ℝ-Algebra y z)
    right-distributive-mul-diff-ℝ-Algebra =
      right-distributive-mul-diff-algebra-Commutative-Ring R A

    left-negative-law-mul-ℝ-Algebra :
      (x y : type-ℝ-Algebra A) →
      mul-ℝ-Algebra (neg-ℝ-Algebra A x) y ＝
      neg-ℝ-Algebra A (mul-ℝ-Algebra x y)
    left-negative-law-mul-ℝ-Algebra =
      left-negative-law-mul-algebra-Commutative-Ring R A

    right-negative-law-mul-ℝ-Algebra :
      (x y : type-ℝ-Algebra A) →
      mul-ℝ-Algebra x (neg-ℝ-Algebra A y) ＝
      neg-ℝ-Algebra A (mul-ℝ-Algebra x y)
    right-negative-law-mul-ℝ-Algebra =
      right-negative-law-mul-algebra-Commutative-Ring R A

    associative-scalar-mul-mul-ℝ-Algebra :
      (c : ℝ l1) (x y : type-ℝ-Algebra A) →
      mul-ℝ-Algebra (scalar-mul-ℝ-Algebra A c x) y ＝
      scalar-mul-ℝ-Algebra A c (mul-ℝ-Algebra x y)
    associative-scalar-mul-mul-ℝ-Algebra =
      associative-scalar-mul-mul-algebra-Commutative-Ring R A

    left-swap-scalar-mul-mul-ℝ-Algebra :
      (c : ℝ l1) (x y : type-ℝ-Algebra A) →
      scalar-mul-ℝ-Algebra A c (mul-ℝ-Algebra x y) ＝
      mul-ℝ-Algebra x (scalar-mul-ℝ-Algebra A c y)
    left-swap-scalar-mul-mul-ℝ-Algebra =
      left-swap-scalar-mul-mul-algebra-Commutative-Ring R A
```
