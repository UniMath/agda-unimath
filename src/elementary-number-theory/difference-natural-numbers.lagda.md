# The difference of natural numbers

```agda
module elementary-number-theory.difference-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.distance-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

Given two [natural numbers](elementary-number-theory.natural-numbers.md) `a` and
`b`, there is a difference `a - b` such that the
[sum](elementary-number-theory.addition-natural-numbers.md) of `a - b` and `b`
is `a` if and only if `b` is
[less than or equal to](elementary-number-theory.inequality-natural-numbers.md)
`a`.

**Note.** The difference of `a` and `b` is equivalent to the
[distance](elementary-number-theory.distance-natural-numbers.md) between `a` and
`b`, but is only defined when `b ≤ a`. For this reason, it is often preferred to use
the distance function over the difference function on natural numbers.

## Definition

### The difference of natural numbers

```agda
diff-leq-ℕ : (a b : ℕ) → leq-ℕ b a → ℕ
diff-leq-ℕ a 0 star = a
diff-leq-ℕ (succ-ℕ a) (succ-ℕ b) b≤a = diff-leq-ℕ a b b≤a

abstract
  left-add-diff-leq-ℕ :
    (a b : ℕ) (b≤a : leq-ℕ b a) → diff-leq-ℕ a b b≤a +ℕ b ＝ a
  left-add-diff-leq-ℕ a 0 star = refl
  left-add-diff-leq-ℕ (succ-ℕ a) (succ-ℕ b) b≤a =
    ap succ-ℕ (left-add-diff-leq-ℕ a b b≤a)

  right-add-diff-leq-ℕ :
    (a b : ℕ) (b≤a : leq-ℕ b a) → b +ℕ diff-leq-ℕ a b b≤a ＝ a
  right-add-diff-leq-ℕ a b b≤a =
    commutative-add-ℕ b (diff-leq-ℕ a b b≤a) ∙ left-add-diff-leq-ℕ a b b≤a
```

### The type of differences of two natural numbers

```agda
type-subtraction-ℕ : Relation lzero ℕ
type-subtraction-ℕ n m = Σ ℕ (λ l → l +ℕ n ＝ m)

abstract
  all-elements-equal-type-subtraction-ℕ :
    (n m : ℕ) → all-elements-equal (type-subtraction-ℕ n m)
  all-elements-equal-type-subtraction-ℕ n m (k , k+n=m) (l , l+n=m) =
    eq-type-subtype
      ( λ x → Id-Prop ℕ-Set (x +ℕ n) m)
      ( is-injective-right-add-ℕ n (k+n=m ∙ inv l+n=m))

  is-prop-type-subtraction-ℕ :
    (n m : ℕ) → is-prop (type-subtraction-ℕ n m)
  is-prop-type-subtraction-ℕ n m =
    is-prop-all-elements-equal (all-elements-equal-type-subtraction-ℕ n m)

subtraction-prop-ℕ : Relation-Prop lzero ℕ
subtraction-prop-ℕ n m =
  ( type-subtraction-ℕ n m , is-prop-type-subtraction-ℕ n m)
```

## Properties

### We have `n ≤ m` if and only if there is a number `l` such that `l + n = m`

```agda
subtraction-leq-ℕ : (n m : ℕ) → n ≤-ℕ m → type-subtraction-ℕ n m
subtraction-leq-ℕ n m n≤m = (diff-leq-ℕ m n n≤m , left-add-diff-leq-ℕ m n n≤m)

abstract
  leq-subtraction-ℕ : (n m l : ℕ) → l +ℕ n ＝ m → n ≤-ℕ m
  leq-subtraction-ℕ zero-ℕ m l p = leq-zero-ℕ m
  leq-subtraction-ℕ (succ-ℕ n) (succ-ℕ m) l p =
    leq-subtraction-ℕ n m l (is-injective-succ-ℕ p)

subtraction-iff-leq-ℕ : (n m : ℕ) → n ≤-ℕ m ↔ type-subtraction-ℕ n m
subtraction-iff-leq-ℕ n m =
  ( subtraction-leq-ℕ n m , ind-Σ (leq-subtraction-ℕ n m))
```

### Differences are preserved by addition

```agda
abstract
  diff-right-add-leq-ℕ :
    (k m n : ℕ) (n≤m : leq-ℕ n m) →
    diff-leq-ℕ (m +ℕ k) (n +ℕ k) (preserves-leq-left-add-ℕ k n m n≤m) ＝
    diff-leq-ℕ m n n≤m
  diff-right-add-leq-ℕ 0 m n n≤m =
    ap (diff-leq-ℕ m n) (eq-is-prop (is-prop-leq-ℕ n m))
  diff-right-add-leq-ℕ (succ-ℕ k) m n n≤m =
    ( ap
      ( diff-leq-ℕ (m +ℕ k) (n +ℕ k))
      ( eq-is-prop (is-prop-leq-ℕ (n +ℕ k) (m +ℕ k)))) ∙
    ( diff-right-add-leq-ℕ k m n n≤m)

  diff-left-add-leq-ℕ :
    (k m n : ℕ) (n≤m : leq-ℕ n m) →
    diff-leq-ℕ (k +ℕ m) (k +ℕ n) (preserves-leq-right-add-ℕ k n m n≤m) ＝
    diff-leq-ℕ m n n≤m
  diff-left-add-leq-ℕ k m n n≤m =
    is-injective-right-add-ℕ
      ( k +ℕ n)
      ( equational-reasoning
        ( diff-leq-ℕ (k +ℕ m) (k +ℕ n) (preserves-leq-right-add-ℕ k n m n≤m)) +ℕ
        ( k +ℕ n)
        ＝ k +ℕ m
          by
            left-add-diff-leq-ℕ
              ( k +ℕ m)
              ( k +ℕ n)
              ( preserves-leq-right-add-ℕ k n m n≤m)
        ＝ k +ℕ (diff-leq-ℕ m n n≤m +ℕ n)
          by ap-add-ℕ refl (inv (left-add-diff-leq-ℕ m n n≤m))
        ＝ diff-leq-ℕ m n n≤m +ℕ (k +ℕ n)
          by left-swap-add-ℕ k (diff-leq-ℕ m n n≤m) n)
```

### Where defined, the distance and difference of natural numbers agree

```agda
abstract
  eq-diff-dist-leq-ℕ :
    (m n : ℕ) (n≤m : leq-ℕ n m) → diff-leq-ℕ m n n≤m ＝ dist-ℕ m n
  eq-diff-dist-leq-ℕ 0 0 star = refl
  eq-diff-dist-leq-ℕ (succ-ℕ m) 0 star = refl
  eq-diff-dist-leq-ℕ (succ-ℕ m) (succ-ℕ n) m≤n = eq-diff-dist-leq-ℕ m n m≤n
```

## See also

- [The distance between natural numbers](elementary-number-theory.distance-natural-numbers.md), which is a total function substitute for the difference function considered on this page
