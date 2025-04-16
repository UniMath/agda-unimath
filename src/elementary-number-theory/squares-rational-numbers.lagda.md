# Squares in the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.squares-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.dependent-pair-types
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
```

</details>

## Definition

```agda
square-ℚ : ℚ → ℚ
square-ℚ a = mul-ℚ a a

is-square-ℚ : ℚ → UU lzero
is-square-ℚ a = Σ ℚ (λ x → a ＝ square-ℚ x)

square-root-ℚ : (a : ℚ) → is-square-ℚ a → ℚ
square-root-ℚ _ (root , _) = root
```

## Properties

### Squares in ℚ are nonnegative

```agda
is-nonnegative-square-ℚ : (a : ℚ) → is-nonnegative-ℚ (square-ℚ a)
is-nonnegative-square-ℚ a =
  rec-coproduct
    ( λ H → is-nonnegative-is-positive-ℚ (is-positive-mul-negative-ℚ H H))
    ( λ H → is-nonnegative-mul-ℚ H H)
    ( decide-is-negative-is-nonnegative-ℚ {a})
```

### The square of the negation of `x` is the square of `x`

```agda
abstract
  square-neg-ℚ : (x : ℚ) → square-ℚ (neg-ℚ x) ＝ square-ℚ x
  square-neg-ℚ x =
    equational-reasoning
      neg-ℚ x *ℚ neg-ℚ x
      ＝ neg-ℚ (x *ℚ neg-ℚ x) by left-negative-law-mul-ℚ x (neg-ℚ x)
      ＝ neg-ℚ (neg-ℚ (x *ℚ x)) by ap neg-ℚ (right-negative-law-mul-ℚ x x)
      ＝ x *ℚ x by neg-neg-ℚ (x *ℚ x)
```

### The squares in ℚ are exactly the squares in ℕ

```agda
is-square-int-is-square-nat : {n : ℕ} → is-square-ℕ n → is-square-ℚ (int-ℕ n)
is-square-int-is-square-nat (root , pf-square) =
  ( ( int-ℕ root) ,
    ( ( ap int-ℕ pf-square) ∙
      ( inv (mul-int-ℕ root root))))

is-square-nat-is-square-int : {a : ℚ} → is-square-ℚ a → is-square-ℕ (abs-ℚ a)
is-square-nat-is-square-int (root , pf-square) =
  ( ( abs-ℚ root) ,
    ( ( ap abs-ℚ pf-square) ∙
      ( multiplicative-abs-ℚ root root)))

iff-is-square-int-is-square-nat :
  (n : ℕ) → is-square-ℕ n ↔ is-square-ℚ (int-ℕ n)
pr1 (iff-is-square-int-is-square-nat n) = is-square-int-is-square-nat
pr2 (iff-is-square-int-is-square-nat n) H =
  tr is-square-ℕ (abs-int-ℕ n) (is-square-nat-is-square-int H)

iff-is-nonneg-square-nat-is-square-int :
  (a : ℚ) → is-square-ℚ a ↔ is-nonnegative-ℚ a × is-square-ℕ (abs-ℚ a)
pr1 (iff-is-nonneg-square-nat-is-square-int a) (root , pf-square) =
  ( ( tr is-nonnegative-ℚ (inv pf-square) (is-nonnegative-square-ℚ root)) ,
    ( is-square-nat-is-square-int (root , pf-square)))
pr2
  ( iff-is-nonneg-square-nat-is-square-int a) (pf-nonneg , (root , pf-square)) =
  ( ( int-ℕ root) ,
    ( ( inv (int-abs-is-nonnegative-ℚ a pf-nonneg)) ∙
      ( pr2 (is-square-int-is-square-nat (root , pf-square)))))
```

### Squareness in ℚ is decidable

```agda
is-decidable-is-square-ℚ : (a : ℚ) → is-decidable (is-square-ℚ a)
is-decidable-is-square-ℚ (inl n) =
  inr (map-neg (pr1 (iff-is-nonneg-square-nat-is-square-int (inl n))) pr1)
is-decidable-is-square-ℚ (inr (inl n)) = inl (zero-ℚ , refl)
is-decidable-is-square-ℚ (inr (inr n)) =
  is-decidable-iff
    ( is-square-int-is-square-nat)
    ( is-square-nat-is-square-int)
    ( is-decidable-is-square-ℕ (succ-ℕ n))
```

### `(x + y)² = x² + 2xy + y²`

```agda
abstract
  square-add-ℚ :
    (x y : ℚ) →
    square-ℚ (x +ℚ y) ＝
    square-ℚ x +ℚ (int-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y
  square-add-ℚ x y =
    equational-reasoning
      square-ℚ (x +ℚ y)
      ＝ x *ℚ (x +ℚ y) +ℚ y *ℚ (x +ℚ y)
        by right-distributive-mul-add-ℚ x y (x +ℚ y)
      ＝ (x *ℚ x +ℚ x *ℚ y) +ℚ (y *ℚ x +ℚ y *ℚ y)
        by
          ap-add-ℚ
            ( left-distributive-mul-add-ℚ x x y)
            ( left-distributive-mul-add-ℚ y x y)
      ＝ x *ℚ x +ℚ (x *ℚ y +ℚ (y *ℚ x +ℚ y *ℚ y))
        by associative-add-ℚ (x *ℚ x) (x *ℚ y) _
      ＝ x *ℚ x +ℚ (x *ℚ y +ℚ (x *ℚ y +ℚ y *ℚ y))
        by
          ap
            ( x *ℚ x +ℚ_)
            ( ap (x *ℚ y +ℚ_) (ap (_+ℚ y *ℚ y) (commutative-mul-ℚ y x)))
      ＝ x *ℚ x +ℚ (int-ℕ 2 *ℚ (x *ℚ y) +ℚ y *ℚ y)
        by ap (x *ℚ x +ℚ_) (inv (associative-add-ℚ (x *ℚ y) (x *ℚ y) (y *ℚ y)))
      ＝ x *ℚ x +ℚ int-ℕ 2 *ℚ (x *ℚ y) +ℚ y *ℚ y
        by inv (associative-add-ℚ (x *ℚ x) (int-ℕ 2 *ℚ (x *ℚ y)) _)

  square-diff-ℚ :
    (x y : ℚ) →
    square-ℚ (x -ℚ y) ＝
    square-ℚ x -ℚ (int-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y
  square-diff-ℚ x y =
    equational-reasoning
      square-ℚ (x -ℚ y)
      ＝ square-ℚ x +ℚ int-ℕ 2 *ℚ (x *ℚ neg-ℚ y) +ℚ square-ℚ (neg-ℚ y)
        by square-add-ℚ x (neg-ℚ y)
      ＝ square-ℚ x +ℚ (int-ℕ 2 *ℚ neg-ℚ (x *ℚ y)) +ℚ square-ℚ y
        by
          ap-add-ℚ
            ( ap (x *ℚ x +ℚ_) (ap (int-ℕ 2 *ℚ_) (right-negative-law-mul-ℚ x y)))
            ( square-neg-ℚ y)
      ＝ square-ℚ x -ℚ (int-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y
        by
          ap
            ( λ z → square-ℚ x +ℚ z +ℚ square-ℚ y)
            ( right-negative-law-mul-ℚ (int-ℕ 2) (x *ℚ y))
```
