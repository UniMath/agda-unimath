# Squares in the natural numbers

```agda
module elementary-number-theory.squares-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.decidable-types
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
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

```agda
abstract
  square-succ-ℕ :
    (n : ℕ) →
    square-ℕ (succ-ℕ n) ＝ succ-ℕ ((succ-ℕ (succ-ℕ n)) *ℕ n)
  square-succ-ℕ n =
    ( right-successor-law-mul-ℕ (succ-ℕ n) n) ∙
    ( commutative-add-ℕ (succ-ℕ n) ((succ-ℕ n) *ℕ n))

  square-succ-succ-ℕ :
    (n : ℕ) →
    square-ℕ (succ-ℕ (succ-ℕ n)) ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ 2 *ℕ n +ℕ 4
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
```

### Squaring distributes over multiplication

```agda
abstract
  distributive-square-mul-ℕ :
    (m n : ℕ) → square-ℕ (m *ℕ n) ＝ square-ℕ m *ℕ square-ℕ n
  distributive-square-mul-ℕ m n = interchange-law-mul-mul-ℕ m n m n
```

### `n > √n` for `n > 1`

The idea is to assume `n = m + 2 ≤ sqrt(m + 2)` for some `m : ℕ` and derive a
contradiction by squaring both sides of the inequality

```agda
abstract
  greater-than-square-root-ℕ :
    (n root : ℕ) → ¬ ((n +ℕ 2 ≤-ℕ root) × (n +ℕ 2 ＝ square-ℕ root))
  greater-than-square-root-ℕ n root (pf-leq , pf-eq) =
    reflects-leq-left-add-ℕ
      ( square-ℕ root)
      ( square-ℕ n +ℕ 2 *ℕ n +ℕ n +ℕ 2)
      ( 0)
      ( tr
        ( leq-ℕ (square-ℕ n +ℕ 2 *ℕ n +ℕ n +ℕ 2 +ℕ square-ℕ root))
        ( inv (left-unit-law-add-ℕ (square-ℕ root)))
        ( concatenate-eq-leq-ℕ
          ( square-ℕ root)
          ( inv
            ( lemma ∙
              ( ap-add-ℕ {square-ℕ n +ℕ 2 *ℕ n +ℕ n +ℕ 2} {n +ℕ 2}
                ( refl)
                ( pf-eq))))
          ( preserves-leq-mul-ℕ (n +ℕ 2) root (n +ℕ 2) root pf-leq pf-leq)))
    where
    lemma : square-ℕ (n +ℕ 2) ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ n +ℕ 2 +ℕ n +ℕ 2
    lemma =
      equational-reasoning
      square-ℕ (n +ℕ 2)
      ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ 2 *ℕ n +ℕ 4
        by (square-succ-succ-ℕ n)
      ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ (n +ℕ 2 +ℕ n +ℕ 2)
        by
          ( ap-add-ℕ {square-ℕ n +ℕ 2 *ℕ n} {2 *ℕ n +ℕ 4}
            ( refl)
            ( equational-reasoning
              2 *ℕ n +ℕ 4
              ＝ n +ℕ n +ℕ 2 +ℕ 2
                by
                  ( ap-add-ℕ {2 *ℕ n} {4}
                    ( left-two-law-mul-ℕ n)
                    ( refl))
              ＝ n +ℕ 2 +ℕ 2 +ℕ n
                by (commutative-add-ℕ n (n +ℕ 2 +ℕ 2))
              ＝ n +ℕ 2 +ℕ (2 +ℕ n)
                by (associative-add-ℕ (n +ℕ 2) 2 n)
              ＝ n +ℕ 2 +ℕ (n +ℕ 2)
                by
                  ( ap-add-ℕ {n +ℕ 2} {2 +ℕ n}
                    ( refl)
                    ( commutative-add-ℕ 2 n))))
      ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ n +ℕ 2 +ℕ n +ℕ 2
        by
          ( inv
            ( associative-add-ℕ
              ( square-ℕ n +ℕ 2 *ℕ n)
              ( n +ℕ 2)
              ( n +ℕ 2)))
```

### Squareness in ℕ is decidable

```agda
is-decidable-big-root :
  (n : ℕ) → is-decidable (Σ ℕ (λ root → (n ≤-ℕ root) × (n ＝ square-ℕ root)))
is-decidable-big-root 0 = inl (0 , star , refl)
is-decidable-big-root 1 = inl (1 , star , refl)
is-decidable-big-root (succ-ℕ (succ-ℕ n)) =
  inr (λ H → greater-than-square-root-ℕ n (pr1 H) (pr2 H))

is-decidable-is-square-ℕ : (n : ℕ) → is-decidable (is-square-ℕ n)
is-decidable-is-square-ℕ n =
  is-decidable-Σ-ℕ n
    ( λ x → n ＝ square-ℕ x)
    ( λ x → has-decidable-equality-ℕ n (square-ℕ x))
    ( is-decidable-big-root n)
```

## See also

- [Cubes of natural numbers](elementary-number-theory.cubes-natural-numbers.md)
