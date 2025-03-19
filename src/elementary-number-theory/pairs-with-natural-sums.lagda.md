# Pairs of natural numbers with a given sum

```agda
module elementary-number-theory.pairs-with-natural-sums where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A pair of natural numbers with a specific known sum resembles an
[integer partition](elementary-number-theory.integer-partitions.md), but is
ordered, and the components may be zero.

## Definition

```agda
pair-with-sum-ℕ : ℕ → UU lzero
pair-with-sum-ℕ n = Σ ℕ ( λ a → Σ ℕ (λ b → b +ℕ a ＝ n))
```

## Properties

### Equivalence of dependent pairs further partitioning a component

```agda
module _
  (n : ℕ)
  where

  map-equiv-pair-with-sum-pr1-pr2 :
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1) →
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2)
  pr1 (map-equiv-pair-with-sum-pr1-pr2 ((p , c , c+p=n) , _)) =
    (c , p , commutative-add-ℕ p c ∙ c+p=n)
  pr2 (map-equiv-pair-with-sum-pr1-pr2 (_ , y)) = y

  map-inv-equiv-pair-with-sum-pr1-pr2 :
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2) →
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1)
  pr1 (map-inv-equiv-pair-with-sum-pr1-pr2 ((c , p , p+c=n) , _)) =
    (p , c , commutative-add-ℕ c p ∙ p+c=n)
  pr2 (map-inv-equiv-pair-with-sum-pr1-pr2 (_ , y)) = y

  is-section-map-inv-equiv-pair-with-sum-pr1-pr2 :
    is-section
      map-equiv-pair-with-sum-pr1-pr2
      map-inv-equiv-pair-with-sum-pr1-pr2
  is-section-map-inv-equiv-pair-with-sum-pr1-pr2
    x@(y@(c , p , p+c=n) , a , b , b+a=p) =
      eq-pair-Σ
        ( eq-pair-Σ refl (eq-pair-Σ refl (eq-type-Prop (Id-Prop ℕ-Set _ _))))
        {!   !}

  is-retraction-map-inv-equiv-pair-with-sum-pr1-pr2 :
    is-retraction
      map-equiv-pair-with-sum-pr1-pr2
      map-inv-equiv-pair-with-sum-pr1-pr2
  is-retraction-map-inv-equiv-pair-with-sum-pr1-pr2
    ((p , c , c+p=n) , a , b , b+a=p) =
      eq-pair-Σ
        ( eq-pair-Σ refl (eq-pair-Σ refl (eq-type-Prop (Id-Prop ℕ-Set _ _))))
        {!   !}

  equiv-pair-with-sum-pr1-pr2 :
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1) ≃
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2)
  equiv-pair-with-sum-pr1-pr2 =
    map-equiv-pair-with-sum-pr1-pr2 ,
    ( map-inv-equiv-pair-with-sum-pr1-pr2 ,
      is-section-map-inv-equiv-pair-with-sum-pr1-pr2) ,
    ( map-inv-equiv-pair-with-sum-pr1-pr2 ,
      is-retraction-map-inv-equiv-pair-with-sum-pr1-pr2)
```
