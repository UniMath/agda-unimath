# Squares in the integers

```agda
module elementary-number-theory.squares-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.squares-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.transport-along-identifications
```

</details>

## Definition

```agda
square-ℤ : ℤ → ℤ
square-ℤ a = mul-ℤ a a

cube-ℤ : ℤ → ℤ
cube-ℤ a = mul-ℤ (square-ℤ a) a

is-square-ℤ : ℤ → UU lzero
is-square-ℤ a = Σ ℤ (λ x → a ＝ square-ℤ x)

square-root-ℤ : (a : ℤ) → is-square-ℤ a → ℤ
square-root-ℤ _ (root , _) = root
```

## Properties

### Squares in ℤ are nonnegative

```agda
is-nonnegative-square-ℤ : (a : ℤ) → is-nonnegative-ℤ (square-ℤ a)
is-nonnegative-square-ℤ a =
  rec-coproduct
    ( λ H → is-nonnegative-is-positive-ℤ (is-positive-mul-negative-ℤ H H))
    ( λ H → is-nonnegative-mul-ℤ H H)
    ( decide-is-negative-is-nonnegative-ℤ {a})
```

### The square of the negation of `x` is the square of `x`

```agda
abstract
  square-neg-ℤ : (x : ℤ) → square-ℤ (neg-ℤ x) ＝ square-ℤ x
  square-neg-ℤ x =
    equational-reasoning
      neg-ℤ x *ℤ neg-ℤ x
      ＝ neg-ℤ (x *ℤ neg-ℤ x) by left-negative-law-mul-ℤ x (neg-ℤ x)
      ＝ neg-ℤ (neg-ℤ (x *ℤ x)) by ap neg-ℤ (right-negative-law-mul-ℤ x x)
      ＝ x *ℤ x by neg-neg-ℤ (x *ℤ x)
```

### The squares in ℤ are exactly the squares in ℕ

```agda
is-square-int-is-square-nat : {n : ℕ} → is-square-ℕ n → is-square-ℤ (int-ℕ n)
is-square-int-is-square-nat (root , pf-square) =
  ( ( int-ℕ root) ,
    ( ( ap int-ℕ pf-square) ∙
      ( inv (mul-int-ℕ root root))))

is-square-nat-is-square-int : {a : ℤ} → is-square-ℤ a → is-square-ℕ (abs-ℤ a)
is-square-nat-is-square-int (root , pf-square) =
  ( ( abs-ℤ root) ,
    ( ( ap abs-ℤ pf-square) ∙
      ( multiplicative-abs-ℤ root root)))

iff-is-square-int-is-square-nat :
  (n : ℕ) → is-square-ℕ n ↔ is-square-ℤ (int-ℕ n)
pr1 (iff-is-square-int-is-square-nat n) = is-square-int-is-square-nat
pr2 (iff-is-square-int-is-square-nat n) H =
  tr is-square-ℕ (abs-int-ℕ n) (is-square-nat-is-square-int H)

iff-is-nonneg-square-nat-is-square-int :
  (a : ℤ) → is-square-ℤ a ↔ is-nonnegative-ℤ a × is-square-ℕ (abs-ℤ a)
pr1 (iff-is-nonneg-square-nat-is-square-int a) (root , pf-square) =
  ( ( tr is-nonnegative-ℤ (inv pf-square) (is-nonnegative-square-ℤ root)) ,
    ( is-square-nat-is-square-int (root , pf-square)))
pr2
  ( iff-is-nonneg-square-nat-is-square-int a) (pf-nonneg , (root , pf-square)) =
  ( ( int-ℕ root) ,
    ( ( inv (int-abs-is-nonnegative-ℤ a pf-nonneg)) ∙
      ( pr2 (is-square-int-is-square-nat (root , pf-square)))))
```

### Squareness in ℤ is decidable

```agda
is-decidable-is-square-ℤ : (a : ℤ) → is-decidable (is-square-ℤ a)
is-decidable-is-square-ℤ (inl n) =
  inr (map-neg (pr1 (iff-is-nonneg-square-nat-is-square-int (inl n))) pr1)
is-decidable-is-square-ℤ (inr (inl n)) = inl (zero-ℤ , refl)
is-decidable-is-square-ℤ (inr (inr n)) =
  is-decidable-iff
    ( is-square-int-is-square-nat)
    ( is-square-nat-is-square-int)
    ( is-decidable-is-square-ℕ (succ-ℕ n))
```

### The square of a sum

We have the identity `(x + y)² = x² + 2xy + y²` for the square of a sum.

```agda
abstract
  square-add-ℤ :
    (x y : ℤ) →
    square-ℤ (x +ℤ y) ＝
    square-ℤ x +ℤ (int-ℕ 2 *ℤ (x *ℤ y)) +ℤ square-ℤ y
  square-add-ℤ x y =
    equational-reasoning
      square-ℤ (x +ℤ y)
      ＝ x *ℤ (x +ℤ y) +ℤ y *ℤ (x +ℤ y)
        by right-distributive-mul-add-ℤ x y (x +ℤ y)
      ＝ (x *ℤ x +ℤ x *ℤ y) +ℤ (y *ℤ x +ℤ y *ℤ y)
        by
          ap-add-ℤ
            ( left-distributive-mul-add-ℤ x x y)
            ( left-distributive-mul-add-ℤ y x y)
      ＝ x *ℤ x +ℤ (x *ℤ y +ℤ (y *ℤ x +ℤ y *ℤ y))
        by associative-add-ℤ (x *ℤ x) (x *ℤ y) _
      ＝ x *ℤ x +ℤ (x *ℤ y +ℤ (x *ℤ y +ℤ y *ℤ y))
        by
          ap
            ( x *ℤ x +ℤ_)
            ( ap (x *ℤ y +ℤ_) (ap (_+ℤ y *ℤ y) (commutative-mul-ℤ y x)))
      ＝ x *ℤ x +ℤ (int-ℕ 2 *ℤ (x *ℤ y) +ℤ y *ℤ y)
        by ap (x *ℤ x +ℤ_) (inv (associative-add-ℤ (x *ℤ y) (x *ℤ y) (y *ℤ y)))
      ＝ x *ℤ x +ℤ int-ℕ 2 *ℤ (x *ℤ y) +ℤ y *ℤ y
        by inv (associative-add-ℤ (x *ℤ x) (int-ℕ 2 *ℤ (x *ℤ y)) _)
```

### The square of a difference

We have the identity `(x - y)² = x² - 2xy + y²` for the square of a difference.

```agda
  square-diff-ℤ :
    (x y : ℤ) →
    square-ℤ (x -ℤ y) ＝
    square-ℤ x -ℤ (int-ℕ 2 *ℤ (x *ℤ y)) +ℤ square-ℤ y
  square-diff-ℤ x y =
    equational-reasoning
      square-ℤ (x -ℤ y)
      ＝ square-ℤ x +ℤ int-ℕ 2 *ℤ (x *ℤ neg-ℤ y) +ℤ square-ℤ (neg-ℤ y)
        by square-add-ℤ x (neg-ℤ y)
      ＝ square-ℤ x +ℤ (int-ℕ 2 *ℤ neg-ℤ (x *ℤ y)) +ℤ square-ℤ y
        by
          ap-add-ℤ
            ( ap (x *ℤ x +ℤ_) (ap (int-ℕ 2 *ℤ_) (right-negative-law-mul-ℤ x y)))
            ( square-neg-ℤ y)
      ＝ square-ℤ x -ℤ (int-ℕ 2 *ℤ (x *ℤ y)) +ℤ square-ℤ y
        by
          ap
            ( λ z → square-ℤ x +ℤ z +ℤ square-ℤ y)
            ( right-negative-law-mul-ℤ (int-ℕ 2) (x *ℤ y))
```
