# Minimum on the natural numbers

```agda
module elementary-number-theory.minimum-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type

open import order-theory.greatest-lower-bounds-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define the operation of minimum (greatest lower bound) for the natural
numbers.

## Definition

```agda
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ 0 n = 0
min-ℕ (succ-ℕ m) 0 = 0
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

ap-min-ℕ : {x x' y y' : ℕ} → x ＝ x' → y ＝ y' → min-ℕ x y ＝ min-ℕ x' y'
ap-min-ℕ p q = ap-binary min-ℕ p q

min-Fin-ℕ : (n : ℕ) → (Fin (succ-ℕ n) → ℕ) → ℕ
min-Fin-ℕ zero-ℕ f = f (inr star)
min-Fin-ℕ (succ-ℕ n) f = min-ℕ (f (inr star)) (min-Fin-ℕ n (λ k → f (inl k)))
```

## Properties

### The minimum of two natural numbers is a greatest lower bound

```agda
leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ m → k ≤-ℕ n → k ≤-ℕ (min-ℕ m n)
leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H K = star
leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-min-ℕ k m n H K

leq-left-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ m
leq-left-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-left-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-min-ℕ k m n H

leq-right-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ n
leq-right-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-right-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-min-ℕ k m n H

is-greatest-lower-bound-min-ℕ :
  (l m : ℕ) → is-greatest-binary-lower-bound-Poset ℕ-Poset l m (min-ℕ l m)
is-greatest-lower-bound-min-ℕ l m =
  prove-is-greatest-binary-lower-bound-Poset
    ( ℕ-Poset)
    ( leq-left-leq-min-ℕ (min-ℕ l m) l m (refl-leq-ℕ (min-ℕ l m)) ,
      leq-right-leq-min-ℕ (min-ℕ l m) l m (refl-leq-ℕ (min-ℕ l m)))
    ( λ x (H , K) → leq-min-ℕ x l m H K)
```

### The minimum computes to the lesser of the two numbers

```agda
abstract
  leq-left-min-ℕ : (m n : ℕ) → m ≤-ℕ n → min-ℕ m n ＝ m
  leq-left-min-ℕ zero-ℕ n p = refl
  leq-left-min-ℕ (succ-ℕ m) (succ-ℕ n) p = ap succ-ℕ (leq-left-min-ℕ m n p)

  le-left-min-ℕ : (m n : ℕ) → m <-ℕ n → min-ℕ m n ＝ m
  le-left-min-ℕ m n p = leq-left-min-ℕ m n (leq-le-ℕ m n p)

  leq-right-min-ℕ : (m n : ℕ) → n ≤-ℕ m → min-ℕ m n ＝ n
  leq-right-min-ℕ zero-ℕ zero-ℕ p = refl
  leq-right-min-ℕ (succ-ℕ m) zero-ℕ p = refl
  leq-right-min-ℕ (succ-ℕ m) (succ-ℕ n) p = ap succ-ℕ (leq-right-min-ℕ m n p)

  le-right-min-ℕ : (m n : ℕ) → n <-ℕ m → min-ℕ m n ＝ n
  le-right-min-ℕ m n p = leq-right-min-ℕ m n (leq-le-ℕ n m p)
```

### Associativity of `min-ℕ`

```agda
associative-min-ℕ :
  (x y z : ℕ) → min-ℕ (min-ℕ x y) z ＝ min-ℕ x (min-ℕ y z)
associative-min-ℕ zero-ℕ y z = refl
associative-min-ℕ (succ-ℕ x) zero-ℕ zero-ℕ = refl
associative-min-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) = refl
associative-min-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ = refl
associative-min-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  ap succ-ℕ (associative-min-ℕ x y z)
```

### Zero laws for `min-ℕ`

```agda
left-zero-law-min-ℕ : (x : ℕ) → min-ℕ 0 x ＝ 0
left-zero-law-min-ℕ x = refl

right-zero-law-min-ℕ : (x : ℕ) → min-ℕ x 0 ＝ 0
right-zero-law-min-ℕ zero-ℕ = refl
right-zero-law-min-ℕ (succ-ℕ x) = refl
```

### Commutativity of `min-ℕ`

```agda
commutative-min-ℕ : (x y : ℕ) → min-ℕ x y ＝ min-ℕ y x
commutative-min-ℕ zero-ℕ zero-ℕ = refl
commutative-min-ℕ zero-ℕ (succ-ℕ y) = refl
commutative-min-ℕ (succ-ℕ x) zero-ℕ = refl
commutative-min-ℕ (succ-ℕ x) (succ-ℕ y) = ap succ-ℕ (commutative-min-ℕ x y)
```

### `min-ℕ` is idempotent

```agda
idempotent-min-ℕ : (x : ℕ) → min-ℕ x x ＝ x
idempotent-min-ℕ zero-ℕ = refl
idempotent-min-ℕ (succ-ℕ x) = ap succ-ℕ (idempotent-min-ℕ x)
```

### Addition distributes over `min-ℕ`

```agda
left-distributive-add-min-ℕ :
  (x y z : ℕ) → x +ℕ (min-ℕ y z) ＝ min-ℕ (x +ℕ y) (x +ℕ z)
left-distributive-add-min-ℕ zero-ℕ y z =
  ( left-unit-law-add-ℕ (min-ℕ y z)) ∙
  ( ap-min-ℕ (inv (left-unit-law-add-ℕ y)) (inv (left-unit-law-add-ℕ z)))
left-distributive-add-min-ℕ (succ-ℕ x) y z =
  ( left-successor-law-add-ℕ x (min-ℕ y z)) ∙
  ( ( ap succ-ℕ (left-distributive-add-min-ℕ x y z)) ∙
    ( ap-min-ℕ
      ( inv (left-successor-law-add-ℕ x y))
      ( inv (left-successor-law-add-ℕ x z))))

right-distributive-add-min-ℕ :
  (x y z : ℕ) → (min-ℕ x y) +ℕ z ＝ min-ℕ (x +ℕ z) (y +ℕ z)
right-distributive-add-min-ℕ x y z =
  ( commutative-add-ℕ (min-ℕ x y) z) ∙
  ( ( left-distributive-add-min-ℕ z x y) ∙
    ( ap-min-ℕ (commutative-add-ℕ z x) (commutative-add-ℕ z y)))
```
