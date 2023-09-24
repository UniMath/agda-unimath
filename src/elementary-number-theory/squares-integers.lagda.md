# Squares in the Integers

```agda
module elementary-number-theory.squares-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
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
cube-ℤ a = mul-ℕ (square-ℤ a) a

is-square-ℤ : ℤ → UU lzero
is-square-ℤ a = Σ ℤ (λ x → a ＝ square-ℤ x)

square-root-ℤ : (a : ℤ) → is-square-ℤ a → ℤ
square-root-ℤ _ (root , _) = root
```

## Properties

### Squares in ℤ are nonnegative

```agda
is-decidable-nonnegative-square-ℤ :
  (a : ℤ) →
  (is-nonnegative-ℤ a) + (is-nonnegative-ℤ (neg-ℤ a)) →
  is-nonnegative-ℤ (square-ℤ a)
is-decidable-nonnegative-square-ℤ _ (inl x) = is-nonnegative-mul-ℤ x x
is-decidable-nonnegative-square-ℤ a (inr x) =
  tr
    is-nonnegative-ℤ
    ( double-negative-law-mul-ℤ a a)
    ( is-nonnegative-mul-ℤ x x)

is-nonnegative-square-ℤ : (a : ℤ) → is-nonnegative-ℤ (square-ℤ a)
is-nonnegative-square-ℤ a =
  is-decidable-nonnegative-square-ℤ a decide-is-nonnegative-ℤ
```

### The squares in ℤ are exactly the squares in ℕ

```agda
is-square-int-if-is-square-nat : {n : ℕ} → is-square-ℕ n → is-square-ℤ (int-ℕ n)
is-square-int-if-is-square-nat (root , pf-square) =
  ( pair
    ( int-ℕ root)
    ( ( ap int-ℕ pf-square) ∙
      ( inv (mul-int-ℕ root root))))

is-square-nat-if-is-square-int : {a : ℤ} → is-square-ℤ a → is-square-ℕ (abs-ℤ a)
is-square-nat-if-is-square-int (root , pf-square) =
  ( pair
    ( abs-ℤ root)
    ( ( ap abs-ℤ pf-square) ∙
      ( multiplicative-abs-ℤ root root)))

is-nat-square-iff-is-int-square :
  (n : ℕ) → is-square-ℕ n ↔ is-square-ℤ (int-ℕ n)
pr1 (is-nat-square-iff-is-int-square n) = is-square-int-if-is-square-nat
pr2 (is-nat-square-iff-is-int-square n) H =
  tr is-square-ℕ (abs-int-ℕ n) (is-square-nat-if-is-square-int H)

is-int-square-iff-nonneg-nat-square :
  (a : ℤ) → is-square-ℤ a ↔ is-nonnegative-ℤ a × is-square-ℕ (abs-ℤ a)
pr1 (is-int-square-iff-nonneg-nat-square a) (root , pf-square) =
  ( pair
    ( tr is-nonnegative-ℤ (inv pf-square) (is-nonnegative-square-ℤ root))
    ( is-square-nat-if-is-square-int (root , pf-square)))
pr2 (is-int-square-iff-nonneg-nat-square a) (pf-nonneg , (root , pf-square)) =
  ( pair
    ( int-ℕ root)
    ( ( inv (int-abs-is-nonnegative-ℤ a pf-nonneg)) ∙
      ( pr2 (is-square-int-if-is-square-nat (root , pf-square)))))
```

### Squareness in ℤ is decidable

```agda
is-decidable-square-ℤ : (a : ℤ) → is-decidable (is-square-ℤ a)
is-decidable-square-ℤ (inl n) =
  inr (map-neg (pr1 (is-int-square-iff-nonneg-nat-square (inl n))) pr1)
is-decidable-square-ℤ (inr (inl n)) =
  inl (zero-ℤ , refl)
is-decidable-square-ℤ (inr (inr n)) =
  is-decidable-iff
    is-square-int-if-is-square-nat
    is-square-nat-if-is-square-int
    ( is-decidable-square-ℕ (succ-ℕ n))
```
