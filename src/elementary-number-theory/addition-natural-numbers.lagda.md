# Addition on the natural numbers

```agda
module elementary-number-theory.addition-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.negated-equality
open import foundation.sets
```

</details>

## Definition

```agda
add-ℕ : ℕ → ℕ → ℕ
add-ℕ x 0 = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

infixl 35 _+ℕ_
_+ℕ_ = add-ℕ

{-# BUILTIN NATPLUS _+ℕ_ #-}

add-ℕ' : ℕ → ℕ → ℕ
add-ℕ' m n = add-ℕ n m

ap-add-ℕ :
  {m n m' n' : ℕ} → m ＝ m' → n ＝ n' → m +ℕ n ＝ m' +ℕ n'
ap-add-ℕ p q = ap-binary add-ℕ p q
```

## Properties

### The left and right unit laws

```agda
right-unit-law-add-ℕ :
  (x : ℕ) → x +ℕ zero-ℕ ＝ x
right-unit-law-add-ℕ x = refl

left-unit-law-add-ℕ :
  (x : ℕ) → zero-ℕ +ℕ x ＝ x
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-add-ℕ x)
```

### The left and right successor laws

```agda
abstract
  left-successor-law-add-ℕ :
    (x y : ℕ) → (succ-ℕ x) +ℕ y ＝ succ-ℕ (x +ℕ y)
  left-successor-law-add-ℕ x zero-ℕ = refl
  left-successor-law-add-ℕ x (succ-ℕ y) =
    ap succ-ℕ (left-successor-law-add-ℕ x y)

right-successor-law-add-ℕ :
  (x y : ℕ) → x +ℕ (succ-ℕ y) ＝ succ-ℕ (x +ℕ y)
right-successor-law-add-ℕ x y = refl
```

### Addition is associative

```agda
abstract
  associative-add-ℕ :
    (x y z : ℕ) → (x +ℕ y) +ℕ z ＝ x +ℕ (y +ℕ z)
  associative-add-ℕ x y zero-ℕ = refl
  associative-add-ℕ x y (succ-ℕ z) = ap succ-ℕ (associative-add-ℕ x y z)
```

### Addition is commutative

```agda
abstract
  commutative-add-ℕ : (x y : ℕ) → x +ℕ y ＝ y +ℕ x
  commutative-add-ℕ zero-ℕ y = left-unit-law-add-ℕ y
  commutative-add-ℕ (succ-ℕ x) y =
    (left-successor-law-add-ℕ x y) ∙ (ap succ-ℕ (commutative-add-ℕ x y))
```

### Addition by `1` on the left or on the right is the successor

```agda
abstract
  left-one-law-add-ℕ :
    (x : ℕ) → 1 +ℕ x ＝ succ-ℕ x
  left-one-law-add-ℕ x =
    ( left-successor-law-add-ℕ zero-ℕ x) ∙
    ( ap succ-ℕ (left-unit-law-add-ℕ x))

  right-one-law-add-ℕ :
    (x : ℕ) → x +ℕ 1 ＝ succ-ℕ x
  right-one-law-add-ℕ x = refl
```

### Addition by `2` on the left or on the right is the double successor

```agda
abstract
  left-two-law-add-ℕ :
    (x : ℕ) → 2 +ℕ x ＝ succ-ℕ (succ-ℕ x)
  left-two-law-add-ℕ x =
    ( left-successor-law-add-ℕ 1 x) ∙
    ( ap succ-ℕ (left-one-law-add-ℕ x))

  right-two-law-add-ℕ :
    (x : ℕ) → x +ℕ 2 ＝ succ-ℕ (succ-ℕ x)
  right-two-law-add-ℕ x = refl
```

### Interchange law of addition

```agda
abstract
  interchange-law-add-add-ℕ : interchange-law add-ℕ add-ℕ
  interchange-law-add-add-ℕ =
    interchange-law-commutative-and-associative
      add-ℕ
      commutative-add-ℕ
      associative-add-ℕ
```

### Swap laws of addition

```agda
abstract
  left-swap-add-ℕ : (a b c : ℕ) → a +ℕ (b +ℕ c) ＝ b +ℕ (a +ℕ c)
  left-swap-add-ℕ a b c =
    equational-reasoning
      a +ℕ (b +ℕ c)
      ＝ (a +ℕ b) +ℕ c
        by inv (associative-add-ℕ a b c)
      ＝ (b +ℕ a) +ℕ c
        by ap-add-ℕ (commutative-add-ℕ a b) (refl {x = c})
      ＝ b +ℕ (a +ℕ c)
        by associative-add-ℕ b a c

  right-swap-add-ℕ : (a b c : ℕ) → (a +ℕ b) +ℕ c ＝ (a +ℕ c) +ℕ b
  right-swap-add-ℕ a b c =
    equational-reasoning
      (a +ℕ b) +ℕ c
      ＝ a +ℕ (b +ℕ c)
        by associative-add-ℕ a b c
      ＝ a +ℕ (c +ℕ b)
        by ap-add-ℕ (refl {x = a}) (commutative-add-ℕ b c)
      ＝ (a +ℕ c) +ℕ b
        by inv (associative-add-ℕ a c b)
```

### Addition by a fixed element on either side is injective

```agda
abstract
  is-injective-right-add-ℕ : (k : ℕ) → is-injective (_+ℕ k)
  is-injective-right-add-ℕ zero-ℕ = id
  is-injective-right-add-ℕ (succ-ℕ k) p =
    is-injective-right-add-ℕ k (is-injective-succ-ℕ p)

  is-injective-left-add-ℕ : (k : ℕ) → is-injective (k +ℕ_)
  is-injective-left-add-ℕ k {x} {y} p =
    is-injective-right-add-ℕ
      ( k)
      ( commutative-add-ℕ x k ∙ (p ∙ commutative-add-ℕ k y))
```

### Addition by a fixed element on either side is an embedding

```agda
abstract
  is-emb-left-add-ℕ : (x : ℕ) → is-emb (x +ℕ_)
  is-emb-left-add-ℕ x =
    is-emb-is-injective is-set-ℕ (is-injective-left-add-ℕ x)

  is-emb-right-add-ℕ : (x : ℕ) → is-emb (_+ℕ x)
  is-emb-right-add-ℕ x =
    is-emb-is-injective is-set-ℕ (is-injective-right-add-ℕ x)
```

### `x + y ＝ 0` if and only if both `x` and `y` are `0`

```agda
abstract
  is-zero-right-is-zero-add-ℕ :
    (x y : ℕ) → is-zero-ℕ (x +ℕ y) → is-zero-ℕ y
  is-zero-right-is-zero-add-ℕ x zero-ℕ p = refl
  is-zero-right-is-zero-add-ℕ x (succ-ℕ y) p =
    ex-falso (is-nonzero-succ-ℕ (x +ℕ y) p)

  is-zero-left-is-zero-add-ℕ :
    (x y : ℕ) → is-zero-ℕ (x +ℕ y) → is-zero-ℕ x
  is-zero-left-is-zero-add-ℕ x y p =
    is-zero-right-is-zero-add-ℕ y x ((commutative-add-ℕ y x) ∙ p)

  is-zero-summand-is-zero-sum-ℕ :
    (x y : ℕ) → is-zero-ℕ (x +ℕ y) → (is-zero-ℕ x) × (is-zero-ℕ y)
  is-zero-summand-is-zero-sum-ℕ x y p =
    pair (is-zero-left-is-zero-add-ℕ x y p) (is-zero-right-is-zero-add-ℕ x y p)

  is-zero-sum-is-zero-summand-ℕ :
    (x y : ℕ) → (is-zero-ℕ x) × (is-zero-ℕ y) → is-zero-ℕ (x +ℕ y)
  is-zero-sum-is-zero-summand-ℕ .zero-ℕ .zero-ℕ (pair refl refl) = refl
```

### `m ≠ m + n + 1`

```agda
abstract
  neq-add-ℕ :
    (m n : ℕ) → m ≠ m +ℕ (succ-ℕ n)
  neq-add-ℕ (succ-ℕ m) n p =
    neq-add-ℕ m n
      ( ( is-injective-succ-ℕ p) ∙
        ( left-successor-law-add-ℕ m n))
```

## See also

- The commutative monoid of the natural numbers with addition is defined in
  [`monoid-of-natural-numbers-with-addition`](elementary-number-theory.monoid-of-natural-numbers-with-addition.md).
