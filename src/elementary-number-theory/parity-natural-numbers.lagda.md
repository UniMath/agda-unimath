# Parity of the natural numbers

```agda
module elementary-number-theory.parity-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.squares-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Parity" WDID=Q230967 WD="parity"}} partitions the
[natural numbers](elementary-number-theory.natural-numbers.md) into two classes:
the {{#concept "even" WDID=Q13366104 WD="even number" Agda=is-even-ℕ}} and the
{{#concept "odd" WDID=Q13366129 WD="odd number" Agda=is-odd-ℕ}} natural numbers.
Even natural numbers are those that are
[divisible](elementary-number-theory.divisibility-natural-numbers.md) by two,
and odd natural numbers are those that [aren't](foundation.negation.md).

## Definition

```agda
is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = div-ℕ 2 n

is-odd-ℕ : ℕ → UU lzero
is-odd-ℕ n = ¬ (is-even-ℕ n)
```

## Properties

### Being even or odd is decidable

```agda
is-decidable-is-even-ℕ : (x : ℕ) → is-decidable (is-even-ℕ x)
is-decidable-is-even-ℕ x = is-decidable-div-ℕ 2 x

is-decidable-is-odd-ℕ : (x : ℕ) → is-decidable (is-odd-ℕ x)
is-decidable-is-odd-ℕ x = is-decidable-neg (is-decidable-is-even-ℕ x)
```

### Being even or odd is a proposition

```agda
abstract
  is-prop-is-even-ℕ : (n : ℕ) → is-prop (is-even-ℕ n)
  is-prop-is-even-ℕ n = is-prop-div-ℕ 2 n (is-nonzero-nat-nonzero-ℕ two-ℕ⁺)

  is-prop-is-odd-ℕ : (n : ℕ) → is-prop (is-odd-ℕ n)
  is-prop-is-odd-ℕ n = is-prop-neg

is-even-prop-ℕ : ℕ → Prop lzero
is-even-prop-ℕ n = (is-even-ℕ n , is-prop-is-even-ℕ n)

is-odd-prop-ℕ : ℕ → Prop lzero
is-odd-prop-ℕ n = (is-odd-ℕ n , is-prop-is-odd-ℕ n)
```

### `0` is an even natural number

```agda
is-even-zero-ℕ : is-even-ℕ 0
is-even-zero-ℕ = div-zero-ℕ 2

is-odd-one-ℕ : is-odd-ℕ 1
is-odd-one-ℕ H = Eq-eq-ℕ (is-one-div-one-ℕ 2 H)
```

### An odd natural number is nonzero

```agda
abstract
  is-nonzero-is-odd-ℕ : {n : ℕ} → is-odd-ℕ n → is-nonzero-ℕ n
  is-nonzero-is-odd-ℕ odd-n refl = odd-n is-even-zero-ℕ
```

### A natural number `x` is even if and only if `x + 2` is even

```agda
abstract
  is-even-is-even-succ-succ-ℕ :
    (n : ℕ) → is-even-ℕ (succ-ℕ (succ-ℕ n)) → is-even-ℕ n
  pr1 (is-even-is-even-succ-succ-ℕ n (succ-ℕ d , p)) = d
  pr2 (is-even-is-even-succ-succ-ℕ n (succ-ℕ d , p)) =
    is-injective-succ-ℕ (is-injective-succ-ℕ p)

  is-even-succ-succ-is-even-ℕ :
    (n : ℕ) → is-even-ℕ n → is-even-ℕ (succ-ℕ (succ-ℕ n))
  pr1 (is-even-succ-succ-is-even-ℕ n (d , p)) = succ-ℕ d
  pr2 (is-even-succ-succ-is-even-ℕ n (d , p)) = ap (succ-ℕ ∘ succ-ℕ) p
```

### A natural number `x` is odd if and only if `x + 2` is odd

```agda
abstract
  is-odd-is-odd-succ-succ-ℕ :
    (n : ℕ) → is-odd-ℕ (succ-ℕ (succ-ℕ n)) → is-odd-ℕ n
  is-odd-is-odd-succ-succ-ℕ n = map-neg (is-even-succ-succ-is-even-ℕ n)

  is-odd-succ-succ-is-odd-ℕ :
    (n : ℕ) → is-odd-ℕ n → is-odd-ℕ (succ-ℕ (succ-ℕ n))
  is-odd-succ-succ-is-odd-ℕ n = map-neg (is-even-is-even-succ-succ-ℕ n)
```

### If a natural number `x` is odd, then `x + 1` is even

```agda
abstract
  is-even-succ-is-odd-ℕ :
    (n : ℕ) → is-odd-ℕ n → is-even-ℕ (succ-ℕ n)
  is-even-succ-is-odd-ℕ zero-ℕ p = ex-falso (p is-even-zero-ℕ)
  is-even-succ-is-odd-ℕ (succ-ℕ zero-ℕ) p = (1 , refl)
  is-even-succ-is-odd-ℕ (succ-ℕ (succ-ℕ n)) p =
    is-even-succ-succ-is-even-ℕ
      ( succ-ℕ n)
      ( is-even-succ-is-odd-ℕ n (is-odd-is-odd-succ-succ-ℕ n p))
```

### If a natural number `x` is even, then `x + 1` is odd

```agda
abstract
  is-odd-succ-is-even-ℕ :
    (n : ℕ) → is-even-ℕ n → is-odd-ℕ (succ-ℕ n)
  is-odd-succ-is-even-ℕ zero-ℕ p = is-odd-one-ℕ
  is-odd-succ-is-even-ℕ (succ-ℕ zero-ℕ) p = ex-falso (is-odd-one-ℕ p)
  is-odd-succ-is-even-ℕ (succ-ℕ (succ-ℕ n)) p =
    is-odd-succ-succ-is-odd-ℕ
      ( succ-ℕ n)
      ( is-odd-succ-is-even-ℕ n (is-even-is-even-succ-succ-ℕ n p))
```

### If a natural number `x + 1` is odd, then `x` is even

```agda
abstract
  is-even-is-odd-succ-ℕ :
    (n : ℕ) → is-odd-ℕ (succ-ℕ n) → is-even-ℕ n
  is-even-is-odd-succ-ℕ n p =
    is-even-is-even-succ-succ-ℕ
      ( n)
      ( is-even-succ-is-odd-ℕ (succ-ℕ n) p)
```

### If a natural number `x + 1` is even, then `x` is odd

```agda
abstract
  is-odd-is-even-succ-ℕ :
    (n : ℕ) → is-even-ℕ (succ-ℕ n) → is-odd-ℕ n
  is-odd-is-even-succ-ℕ n p =
    is-odd-is-odd-succ-succ-ℕ
      ( n)
      ( is-odd-succ-is-even-ℕ (succ-ℕ n) p)
```

### A natural number `x` is odd if and only if there is a natural number `y` such that `succ-ℕ (y *ℕ 2) ＝ x`

```agda
has-odd-expansion : ℕ → UU lzero
has-odd-expansion x = Σ ℕ (λ y → (succ-ℕ (y *ℕ 2)) ＝ x)

abstract
  is-odd-has-odd-expansion : (n : ℕ) → has-odd-expansion n → is-odd-ℕ n
  is-odd-has-odd-expansion .(succ-ℕ (m *ℕ 2)) (m , refl) =
    is-odd-succ-is-even-ℕ (m *ℕ 2) (m , refl)

  has-odd-expansion-is-odd : (n : ℕ) → is-odd-ℕ n → has-odd-expansion n
  has-odd-expansion-is-odd zero-ℕ p = ex-falso (p is-even-zero-ℕ)
  has-odd-expansion-is-odd (succ-ℕ zero-ℕ) p = 0 , refl
  has-odd-expansion-is-odd (succ-ℕ (succ-ℕ n)) p =
    ( succ-ℕ (pr1 s)) , ap (succ-ℕ ∘ succ-ℕ) (pr2 s)
    where
    s : has-odd-expansion n
    s = has-odd-expansion-is-odd n (is-odd-is-odd-succ-succ-ℕ n p)
```

### If `x` is odd and `y` is even, `x ≠ y`

```agda
abstract
  noneq-odd-even :
    (x y : ℕ) → is-odd-ℕ x → is-even-ℕ y → x ≠ y
  noneq-odd-even x y odd-x even-y x=y = odd-x (inv-tr is-even-ℕ x=y even-y)
```

### If `x` and `y` are odd, `xy` is odd

```agda
abstract
  is-odd-mul-is-odd-ℕ :
    (x y : ℕ) → is-odd-ℕ x → is-odd-ℕ y → is-odd-ℕ (x *ℕ y)
  is-odd-mul-is-odd-ℕ _ _ odd-x odd-y
    with has-odd-expansion-is-odd _ odd-x | has-odd-expansion-is-odd _ odd-y
  ... | (m , refl) | (n , refl) =
    is-odd-has-odd-expansion _
      ( m *ℕ (2 *ℕ n) +ℕ m +ℕ n ,
        ( equational-reasoning
          succ-ℕ ((m *ℕ (2 *ℕ n) +ℕ m +ℕ n) *ℕ 2)
          ＝ succ-ℕ ((m *ℕ (2 *ℕ n) +ℕ m) *ℕ 2 +ℕ n *ℕ 2)
            by ap succ-ℕ (right-distributive-mul-add-ℕ (m *ℕ (2 *ℕ n) +ℕ m) n 2)
          ＝ (m *ℕ (2 *ℕ n) +ℕ (m *ℕ 1)) *ℕ 2 +ℕ succ-ℕ (n *ℕ 2)
            by
              ap
                ( λ k → succ-ℕ ((m *ℕ (2 *ℕ n) +ℕ k) *ℕ 2 +ℕ n *ℕ 2))
                ( inv (right-unit-law-mul-ℕ m))
          ＝ m *ℕ (2 *ℕ n +ℕ 1) *ℕ 2 +ℕ succ-ℕ (n *ℕ 2)
            by
              ap
                ( λ k → k *ℕ 2 +ℕ succ-ℕ (n *ℕ 2))
                ( inv (left-distributive-mul-add-ℕ m (2 *ℕ n) 1))
          ＝ m *ℕ 2 *ℕ succ-ℕ (2 *ℕ n) +ℕ succ-ℕ (n *ℕ 2)
            by ap (_+ℕ succ-ℕ (n *ℕ 2)) (right-swap-mul-ℕ m (succ-ℕ (2 *ℕ n)) 2)
          ＝ m *ℕ 2 *ℕ succ-ℕ (n *ℕ 2) +ℕ 1 *ℕ succ-ℕ (n *ℕ 2)
            by
              ap-add-ℕ
                ( ap (λ k → m *ℕ 2 *ℕ succ-ℕ k) (commutative-mul-ℕ 2 n))
                ( inv (left-unit-law-mul-ℕ (succ-ℕ (n *ℕ 2))))
          ＝ succ-ℕ (m *ℕ 2) *ℕ succ-ℕ (n *ℕ 2)
            by inv (right-distributive-mul-add-ℕ (m *ℕ 2) 1 (succ-ℕ (n *ℕ 2)))))
```

### If `xy` is even, `x` or `y` is even

```agda
abstract
  is-even-either-factor-is-even-mul-ℕ :
    (x y : ℕ) → is-even-ℕ (x *ℕ y) → (is-even-ℕ x) + (is-even-ℕ y)
  is-even-either-factor-is-even-mul-ℕ x y is-even-xy =
    rec-coproduct
      ( inl)
      ( λ is-odd-x →
        rec-coproduct
          ( inr)
          ( λ is-odd-y →
            ex-falso (is-odd-mul-is-odd-ℕ x y is-odd-x is-odd-y is-even-xy))
          ( is-decidable-is-even-ℕ y))
      ( is-decidable-is-even-ℕ x)
```

### If `x²` is even, `x` is even

```agda
abstract
  is-even-is-even-square-ℕ : (x : ℕ) → is-even-ℕ (square-ℕ x) → is-even-ℕ x
  is-even-is-even-square-ℕ x is-even-x² =
    rec-coproduct id id (is-even-either-factor-is-even-mul-ℕ x x is-even-x²)
```
