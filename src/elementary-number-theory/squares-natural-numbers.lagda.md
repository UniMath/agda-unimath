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
open import elementary-number-theory.strict-inequality-natural-numbers

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

For any `n` we have `(n + 1)² ＝ (n + 2)n + 1

```agda
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

### Any number is less than its own square

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
    ( inv (square-succ-ℕ n))
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
    ( inv (square-succ-ℕ (succ-ℕ (succ-ℕ n))))
```

### If a number `n` greater than 1 has a square root, then its square root is strictly smaller than `n`

```agda
strict-upper-bound-square-root-ℕ :
  (n : ℕ) → 1 <-ℕ n → (H : is-square-ℕ n) → square-root-ℕ n H <-ℕ n
strict-upper-bound-square-root-ℕ ._ B (succ-ℕ (succ-ℕ x) , refl) =
  strict-lower-bound-square-ℕ (x +ℕ 2) star
```

### `n > √n` for `n > 1`

The idea is to assume `n = m + 2 ≤ sqrt(m + 2)` for some `m : ℕ` and derive a
contradiction by squaring both sides of the inequality

```agda
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
