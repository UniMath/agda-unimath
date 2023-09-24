# Squares in the Natural Numbers

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

open import foundation.action-on-identifications-functions
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

## Definition

```agda
square-ℕ : ℕ → ℕ
square-ℕ n = mul-ℕ n n

cube-ℕ : ℕ → ℕ
cube-ℕ n = (square-ℕ n) *ℕ n

is-square-ℕ : ℕ → UU lzero
is-square-ℕ n = Σ ℕ (λ x → n ＝ square-ℕ x)

square-root-ℕ : (n : ℕ) → is-square-ℕ n → ℕ
square-root-ℕ _ (root , _) = root
```

## Properties

### Squares of successors

```agda
square-succ-ℕ :
  (k : ℕ) →
  square-ℕ (succ-ℕ k) ＝ succ-ℕ ((succ-ℕ (succ-ℕ k)) *ℕ k)
square-succ-ℕ k =
  ( right-successor-law-mul-ℕ (succ-ℕ k) k) ∙
  ( commutative-add-ℕ (succ-ℕ k) ((succ-ℕ k) *ℕ k))
```

### n > √n for n > 1

The idea is to assume `n = m + 2 ≤ sqrt(m + 2)` for some `m : ℕ` and derive a
contradiction by squaring both sides of the inequality

```agda
greater-than-square-root-ℕ :
  (n root : ℕ) → ¬ ((n +ℕ 2 ≤-ℕ root) × (n +ℕ 2 ＝ square-ℕ root))
greater-than-square-root-ℕ n root (pf-leq , pf-eq) =
  reflects-order-add-ℕ
    ( square-ℕ root)
    ( n *ℕ (n +ℕ 2) +ℕ n +ℕ 2)
    0
    ( tr
      ( leq-ℕ (n *ℕ (n +ℕ 2) +ℕ n +ℕ 2 +ℕ square-ℕ root))
      ( inv (left-unit-law-add-ℕ (square-ℕ root)))
      ( concatenate-eq-leq-ℕ
        ( square-ℕ root)
        ( inv
          ( helper ∙
            ( ap
              ( add-ℕ (n *ℕ (n +ℕ 2) +ℕ n +ℕ 2))
              pf-eq)))
        ( preserves-leq-mul-ℕ (n +ℕ 2) root (n +ℕ 2) root pf-leq pf-leq)))
  where
  helper : square-ℕ (n +ℕ 2) ＝ n *ℕ (n +ℕ 2) +ℕ n +ℕ 2 +ℕ n +ℕ 2
  helper =
    equational-reasoning
    square-ℕ (n +ℕ 2)
    ＝ n *ℕ (n +ℕ 2) +ℕ (2 *ℕ (n +ℕ 2))
      by (right-distributive-mul-add-ℕ n 2 (n +ℕ 2))
    ＝ n *ℕ (n +ℕ 2) +ℕ 2 *ℕ n +ℕ 4
      by
        ( ap
          ( add-ℕ (n *ℕ (n +ℕ 2)))
          ( left-distributive-mul-add-ℕ 2 n 2))
    ＝ n *ℕ (n +ℕ 2) +ℕ (n +ℕ 2 +ℕ (n +ℕ 2))
      by
        ( ap
          ( add-ℕ (n *ℕ (n +ℕ 2)))
          ( equational-reasoning
            2 *ℕ n +ℕ 4
            ＝ 4 +ℕ 2 *ℕ n
              by (commutative-add-ℕ (2 *ℕ n) 4)
            ＝ 2 +ℕ 2 +ℕ (n +ℕ n)
              by
                ( ap
                  ( add-ℕ 4)
                  ( left-two-law-mul-ℕ n))
            ＝ (2 +ℕ 2 +ℕ n) +ℕ n
              by
                ( inv
                  ( associative-add-ℕ 4 n n))
            ＝ n +ℕ (2 +ℕ 2 +ℕ n)
              by (commutative-add-ℕ (2 +ℕ 2 +ℕ n) n)
            ＝ n +ℕ (2 +ℕ (2 +ℕ n))
              by
                ( ap
                  ( add-ℕ n)
                  ( associative-add-ℕ 2 2 n))
            ＝ n +ℕ (2 +ℕ (n +ℕ 2))
              by
                ( ap-add-ℕ {n} {2 +ℕ (2 +ℕ n)}
                  refl
                  ( ap
                    ( add-ℕ 2)
                    ( commutative-add-ℕ 2 n)))
            ＝ n +ℕ 2 +ℕ (n +ℕ 2)
              by
                ( inv
                  ( associative-add-ℕ n 2 (n +ℕ 2)))))
    ＝ n *ℕ (n +ℕ 2) +ℕ n +ℕ 2 +ℕ (n +ℕ 2)
      by
        ( inv
          ( associative-add-ℕ
            ( n *ℕ (n +ℕ 2))
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

is-decidable-square-ℕ : (n : ℕ) → is-decidable (is-square-ℕ n)
is-decidable-square-ℕ n =
  is-decidable-Σ-ℕ n
    ( λ x → n ＝ square-ℕ x)
    ( λ x → has-decidable-equality-ℕ n (square-ℕ x))
    ( is-decidable-big-root n)
```
