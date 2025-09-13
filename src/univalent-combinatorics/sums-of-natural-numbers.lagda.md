# Combinatorial identities of sums of natural numbers

```agda
module univalent-combinatorics.sums-of-natural-numbers where

open import elementary-number-theory.sums-of-natural-numbers public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We use counting methods to prove identities of sums of natural numbers

### Finite sums are associative

```agda
abstract
  associative-sum-count-ℕ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (f : (x : A) → B x → ℕ) →
    sum-count-ℕ count-A (λ x → sum-count-ℕ (count-B x) (f x)) ＝
    sum-count-ℕ (count-Σ count-A count-B) (ind-Σ f)
  associative-sum-count-ℕ {l1} {l2} {A} {B} count-A count-B f =
    ( ( htpy-sum-count-ℕ count-A
        ( λ x →
          inv
          ( number-of-elements-count-Σ
            ( count-B x)
            ( λ y → count-Fin (f x y))))) ∙
      ( inv
        ( number-of-elements-count-Σ count-A
          ( λ x → count-Σ (count-B x) (λ y → count-Fin (f x y)))))) ∙
    ( ( double-counting-equiv
        ( count-Σ count-A (λ x → count-Σ (count-B x) (λ y → count-Fin (f x y))))
        ( count-Σ (count-Σ count-A count-B) (λ x → count-Fin (ind-Σ f x)))
        ( inv-associative-Σ A B (λ x → Fin (ind-Σ f x)))) ∙
      ( number-of-elements-count-Σ
        ( count-Σ count-A count-B)
        ( λ x → (count-Fin (ind-Σ f x)))))
```
