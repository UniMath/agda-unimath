# Squares in the natural numbers

```agda
module elementary-number-theory.squares-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.decidable-types
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The {{#concept "square" Disambiguation="natural number" Agda=square-ℕ}} `n²` of
a [natural number](elementary-number-theory.natural-numbers.md) `n` is the
[product](elementary-number-theory.multiplication-natural-numbers.md)

```text
  n² := n * n
```

of `n` with itself.

## Definition

### Squares of natural numbers

```agda
square-ℕ : ℕ → ℕ
square-ℕ n = mul-ℕ n n
```

### The predicate of being a square of a natural number

```agda
is-square-ℕ : ℕ → UU lzero
is-square-ℕ n = Σ ℕ (λ x → n ＝ square-ℕ x)
```

### The square root of a square natural number

```agda
square-root-ℕ : (n : ℕ) → is-square-ℕ n → ℕ
square-root-ℕ _ (root , _) = root
```

## Properties

### Squares of successors

For any `n` we have the equations

```text
  (n + 1)² ＝ (n + 2)n + 1
  (n + 1)² ＝ n² + 2n + 1.
```

```agda
square-succ-ℕ' :
  (n : ℕ) → square-ℕ (succ-ℕ n) ＝ (n +ℕ 2) *ℕ n +ℕ 1
square-succ-ℕ' n =
  right-successor-law-mul-ℕ (succ-ℕ n) n

square-succ-ℕ : (n : ℕ) → square-ℕ (succ-ℕ n) ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ 1
square-succ-ℕ n =
  square-succ-ℕ' n ∙ ap succ-ℕ (right-distributive-mul-add-ℕ n 2 n)
```

### Squares of double successors

For any `n` we have `(n + 2)² ＝ n² + 4n + 4`

```agda
square-succ-succ-ℕ :
  (n : ℕ) →
  square-ℕ (succ-ℕ (succ-ℕ n)) ＝ square-ℕ n +ℕ 4 *ℕ n +ℕ 4
square-succ-succ-ℕ n =
  equational-reasoning
  square-ℕ (n +ℕ 2)
  ＝ (n +ℕ 2) *ℕ n +ℕ (n +ℕ 2) *ℕ 2
    by (left-distributive-mul-add-ℕ (n +ℕ 2) n 2)
  ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ 2 *ℕ (n +ℕ 2)
    by
      ( ap-add-ℕ {(n +ℕ 2) *ℕ n} {(n +ℕ 2) *ℕ 2}
        ( right-distributive-mul-add-ℕ n 2 n)
        ( commutative-mul-ℕ (n +ℕ 2) 2))
  ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ 2 *ℕ n +ℕ 4
    by
      ( ap-add-ℕ {square-ℕ n +ℕ 2 *ℕ n} {2 *ℕ (n +ℕ 2)}
        ( refl)
        ( left-distributive-mul-add-ℕ 2 n 2))
  ＝ square-ℕ n +ℕ (2 *ℕ n +ℕ 2 *ℕ n +ℕ 4)
    by
      associative-add-ℕ (square-ℕ n) (2 *ℕ n) (2 *ℕ n +ℕ 4)
  ＝ square-ℕ n +ℕ 4 *ℕ n +ℕ 4
    by
      ap
        ( add-ℕ (square-ℕ n))
        ( ap
          ( add-ℕ' 4)
          ( ( inv (associative-add-ℕ (2 *ℕ n) (0 +ℕ n) n)) ∙
            ( inv (ap (add-ℕ' n) (associative-add-ℕ (2 *ℕ n) 0 n)))))
```

### The square function is order preserving

```agda
preserves-order-square-ℕ :
  (m n : ℕ) → m ≤-ℕ n → square-ℕ m ≤-ℕ square-ℕ n
preserves-order-square-ℕ m n H =
  preserves-leq-mul-ℕ m n m n H H

preserves-strict-order-square-ℕ :
  (m n : ℕ) → m <-ℕ n → square-ℕ m <-ℕ square-ℕ n
preserves-strict-order-square-ℕ m n H =
  preserves-strict-order-mul-ℕ m n m n H H
```

### The square function reflects the order on the natural numbers

For any two natural numbers `m` and `n` we have `m² ≤ n² → m ≤ n` and
`m² < n² → m < n`.

```agda
reflects-order-square-ℕ :
  (m n : ℕ) → square-ℕ m ≤-ℕ square-ℕ n → m ≤-ℕ n
reflects-order-square-ℕ m n H =
  leq-not-le-ℕ n m
    ( λ K →
      contradiction-le-ℕ
        ( square-ℕ n)
        ( square-ℕ m)
        ( preserves-strict-order-square-ℕ n m K)
        ( H))

reflects-strict-order-square-ℕ :
  (m n : ℕ) → square-ℕ m <-ℕ square-ℕ n → m <-ℕ n
reflects-strict-order-square-ℕ m n H =
  le-not-leq-ℕ n m
    ( λ K →
      contradiction-le-ℕ
        ( square-ℕ m)
        ( square-ℕ n)
        ( H)
        ( preserves-order-square-ℕ n m K))
```

### Squares distribute over multiplication

```agda
distributive-square-mul-ℕ :
  (m n : ℕ) → square-ℕ (m *ℕ n) ＝ square-ℕ m *ℕ square-ℕ n
distributive-square-mul-ℕ m n =
  interchange-law-mul-mul-ℕ m n m n
```

### Any number is less than or equal to its own square

**Proof.** The proof is by induction. Since `0` is the least natural number, be
base case is trivial. Now consider a natural number `n` such that `n ≤ n²`. Then
we have

```text
  (n + 1 ≤ (n + 1)²) ↔ n + 1 ≤ (n + 2) * n + 1
                     ↔ n ≤ n² + n + n.
```

The last inequality follows by the following chain of inequalities

```text
  n ≤ n²            -- by the induction hypothesis
    ≤ n² + n        -- since a ≤ a + b for any a,b
    ≤ n² + n + n    -- since a ≤ a + b for any a,b
```

```agda
lower-bound-square-ℕ :
  (n : ℕ) → n ≤-ℕ square-ℕ n
lower-bound-square-ℕ zero-ℕ = star
lower-bound-square-ℕ (succ-ℕ n) =
  concatenate-leq-eq-ℕ
    ( succ-ℕ n)
    ( transitive-leq-ℕ
      ( n)
      ( square-ℕ n)
      ( square-ℕ n +ℕ n +ℕ n)
      ( transitive-leq-ℕ
        ( square-ℕ n)
        ( square-ℕ n +ℕ n)
        ( square-ℕ n +ℕ n +ℕ n)
        ( leq-add-ℕ (square-ℕ n +ℕ n) n)
        ( leq-add-ℕ (square-ℕ n) n))
      ( lower-bound-square-ℕ n))
    ( inv (square-succ-ℕ' n))
```

### If a number `n` has a square root, then the square root is at most `n`

```agda
upper-bound-square-root-ℕ :
  (n : ℕ) (H : is-square-ℕ n) → square-root-ℕ n H ≤-ℕ n
upper-bound-square-root-ℕ .(square-ℕ x) (x , refl) =
  lower-bound-square-ℕ x
```

### Any number greater than 1 is strictly less than its square

```agda
strict-lower-bound-square-ℕ :
  (n : ℕ) → 1 <-ℕ n → n <-ℕ square-ℕ n
strict-lower-bound-square-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) H = star
strict-lower-bound-square-ℕ (succ-ℕ (succ-ℕ (succ-ℕ n))) H =
  concatenate-le-eq-ℕ
    { n +ℕ 3}
    ( transitive-le-ℕ
      ( n +ℕ 2)
      ( square-ℕ (n +ℕ 2))
      ( square-ℕ (n +ℕ 2) +ℕ (n +ℕ 2) +ℕ (n +ℕ 2))
      ( strict-lower-bound-square-ℕ (succ-ℕ (succ-ℕ n)) star)
      ( transitive-le-ℕ
        ( square-ℕ (n +ℕ 2))
        ( square-ℕ (n +ℕ 2) +ℕ (n +ℕ 2))
        ( square-ℕ (n +ℕ 2) +ℕ (n +ℕ 2) +ℕ (n +ℕ 2))
        ( le-add-succ-ℕ (square-ℕ (n +ℕ 2)) (n +ℕ 1))
        ( le-add-succ-ℕ (square-ℕ (n +ℕ 2) +ℕ (n +ℕ 2)) (n +ℕ 1))))
    ( inv (square-succ-ℕ' (succ-ℕ (succ-ℕ n))))
```

### If a number `n` greater than 1 has a square root, then its square root is strictly smaller than `n`

```agda
strict-upper-bound-square-root-ℕ :
  (n : ℕ) → 1 <-ℕ n → (H : is-square-ℕ n) → square-root-ℕ n H <-ℕ n
strict-upper-bound-square-root-ℕ ._ B (succ-ℕ (succ-ℕ x) , refl) =
  strict-lower-bound-square-ℕ (x +ℕ 2) star
```

### If `n² ≤ n`, then `n ≤ 1`

```agda
leq-one-leq-square-ℕ :
  (n : ℕ) → square-ℕ n ≤-ℕ n → n ≤-ℕ 1
leq-one-leq-square-ℕ zero-ℕ H = star
leq-one-leq-square-ℕ (succ-ℕ zero-ℕ) H = star
leq-one-leq-square-ℕ (succ-ℕ (succ-ℕ n)) H =
  ex-falso
    ( contradiction-le-ℕ
      ( n +ℕ 2)
      ( square-ℕ (n +ℕ 2))
      ( strict-lower-bound-square-ℕ (n +ℕ 2) star)
      ( H))
```

### If the square root of a perfect square `n` is greater than or equal to `n`, then `n ≤ 1`

```agda
leq-one-leq-square-root-ℕ :
  (n : ℕ) (H : is-square-ℕ n) → n ≤-ℕ square-root-ℕ n H → n ≤-ℕ 1
leq-one-leq-square-root-ℕ ._ (x , refl) H =
  leq-one-leq-square-ℕ (square-ℕ x) (preserves-order-square-ℕ (square-ℕ x) x H)
```

### The strict inequality `n² < n` never holds

```agda
not-le-square-ℕ :
  (n : ℕ) → ¬ (square-ℕ n <-ℕ n)
not-le-square-ℕ n H =
  contradiction-le-ℕ
    ( square-ℕ n)
    ( n)
    ( H)
    ( lower-bound-square-ℕ n)
```

### Being a square natural number is decidable

```agda
has-greater-root-ℕ : (n : ℕ) → UU lzero
has-greater-root-ℕ n = Σ ℕ (λ x → (n ≤-ℕ x) × (n ＝ square-ℕ x))

is-decidable-has-greater-root-ℕ :
  (n : ℕ) → is-decidable (has-greater-root-ℕ n)
is-decidable-has-greater-root-ℕ 0 = inl (0 , star , refl)
is-decidable-has-greater-root-ℕ 1 = inl (1 , star , refl)
is-decidable-has-greater-root-ℕ (succ-ℕ (succ-ℕ n)) =
  inr ( λ (x , b , p) → leq-one-leq-square-root-ℕ (n +ℕ 2) (x , p) b)

is-decidable-is-square-ℕ : (n : ℕ) → is-decidable (is-square-ℕ n)
is-decidable-is-square-ℕ n =
  is-decidable-Σ-ℕ n
    ( λ x → n ＝ square-ℕ x)
    ( λ x → has-decidable-equality-ℕ n (square-ℕ x))
    ( is-decidable-has-greater-root-ℕ n)
```

### Equivalent characterizations of a number being even in terms of its square

Consider a natural number `n`. The following are equivalent:

- The number `n` is even.
- Its square is even.
- Its square is divisible by 4.

```agda
div-four-square-is-even-ℕ :
  (n : ℕ) → is-even-ℕ n → div-ℕ 4 (square-ℕ n)
pr1 (div-four-square-is-even-ℕ .(m *ℕ 2) (m , refl)) =
  square-ℕ m
pr2 (div-four-square-is-even-ℕ .(m *ℕ 2) (m , refl)) =
  inv (distributive-square-mul-ℕ m 2)

is-even-square-is-even-ℕ :
  (n : ℕ) → is-even-ℕ n → is-even-ℕ (square-ℕ n)
is-even-square-is-even-ℕ .(m *ℕ 2) (m , refl) =
  is-even-div-4-ℕ _ (div-four-square-is-even-ℕ (m *ℕ 2) (m , refl))

is-even-is-even-square-ℕ :
  (n : ℕ) → is-even-ℕ (square-ℕ n) → is-even-ℕ n
is-even-is-even-square-ℕ zero-ℕ H = is-even-zero-ℕ
is-even-is-even-square-ℕ (succ-ℕ zero-ℕ) (zero-ℕ , ())
is-even-is-even-square-ℕ (succ-ℕ zero-ℕ) (succ-ℕ k , ())
is-even-is-even-square-ℕ (succ-ℕ (succ-ℕ n)) (m , p) =
  is-even-succ-succ-is-even-ℕ n
    ( is-even-is-even-square-ℕ n
      ( is-even-left-summand-ℕ
        ( square-ℕ n)
        ( 4 *ℕ n)
        ( is-even-div-4-ℕ (4 *ℕ n) (n , commutative-mul-ℕ n 4))
        ( is-even-left-summand-ℕ
          ( square-ℕ n +ℕ 4 *ℕ n)
          ( 4)
          ( 2 , refl)
          ( m , p ∙ square-succ-succ-ℕ n))))

is-even-div-four-square-ℕ :
  (n : ℕ) → div-ℕ 4 (square-ℕ n) → is-even-ℕ n
is-even-div-four-square-ℕ n H =
  is-even-is-even-square-ℕ n (is-even-div-4-ℕ (square-ℕ n) H)
```

## See also

- [Cubes of natural numbers](elementary-number-theory.cubes-natural-numbers.md)
