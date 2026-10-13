# Real algebras

```agda
module linear-algebra.real-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings

open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.real-vector-spaces

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

  type-ℝ-Algebra : UU l2
  type-ℝ-Algebra = type-algebra-Commutative-Ring R A

  diff-ℝ-Algebra : type-ℝ-Algebra → type-ℝ-Algebra → type-ℝ-Algebra
  diff-ℝ-Algebra = diff-algebra-Commutative-Ring R A

  mul-ℝ-Algebra : type-ℝ-Algebra → type-ℝ-Algebra → type-ℝ-Algebra
  mul-ℝ-Algebra = mul-algebra-Commutative-Ring R A
```

## Properties

### Distributivity of multiplication over differences

```agda
module _
  {l1 l2 : Level}
  (A : ℝ-Algebra l1 l2)
  (let R = commutative-ring-ℝ l1)
  where abstract

  left-distributive-mul-diff-ℝ-Algebra :
    (x y z : type-ℝ-Algebra A) →
    mul-ℝ-Algebra A x (diff-ℝ-Algebra A y z) ＝
    diff-ℝ-Algebra A (mul-ℝ-Algebra A x y) (mul-ℝ-Algebra A x z)
  left-distributive-mul-diff-ℝ-Algebra =
    left-distributive-mul-diff-algebra-Commutative-Ring R A

  right-distributive-mul-diff-ℝ-Algebra :
    (x y z : type-ℝ-Algebra A) →
    mul-ℝ-Algebra A (diff-ℝ-Algebra A x y) z ＝
    diff-ℝ-Algebra A
      ( mul-ℝ-Algebra A x z)
      ( mul-ℝ-Algebra A y z)
  right-distributive-mul-diff-ℝ-Algebra =
    right-distributive-mul-diff-algebra-Commutative-Ring R A
```
