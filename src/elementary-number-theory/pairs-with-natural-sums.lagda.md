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
open import foundation.cartesian-product-types
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.conjunction
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

### Equality characterization

```agda
module _
  (n : ℕ)
  where

  Eq-pair-with-sum-ℕ : pair-with-sum-ℕ n → pair-with-sum-ℕ n → UU lzero
  Eq-pair-with-sum-ℕ (a , b , _) (a' , b' , _) = (a ＝ a') × (b ＝ b')

  is-prop-Eq-pair-with-sum-ℕ :
    (x y : pair-with-sum-ℕ n) → is-prop (Eq-pair-with-sum-ℕ x y)
  is-prop-Eq-pair-with-sum-ℕ _ _ =
    is-prop-conjunction-Prop (Id-Prop ℕ-Set _ _) (Id-Prop ℕ-Set _ _)

  refl-Eq-pair-with-sum-ℕ : (x : pair-with-sum-ℕ n) → Eq-pair-with-sum-ℕ x x
  refl-Eq-pair-with-sum-ℕ _ = refl , refl

  eq-Eq-pair-with-sum-ℕ :
    (x y : pair-with-sum-ℕ n) → Eq-pair-with-sum-ℕ x y → x ＝ y
  eq-Eq-pair-with-sum-ℕ x y (refl , refl) =
    eq-pair-eq-fiber (eq-pair-eq-fiber (eq-type-Prop (Id-Prop ℕ-Set _ _)))

  abstract
    is-set-pair-with-sum-ℕ : is-set (pair-with-sum-ℕ n)
    is-set-pair-with-sum-ℕ =
      is-set-prop-in-id
        Eq-pair-with-sum-ℕ
        is-prop-Eq-pair-with-sum-ℕ
        refl-Eq-pair-with-sum-ℕ
        eq-Eq-pair-with-sum-ℕ

  set-pair-with-sum-ℕ : Set lzero
  set-pair-with-sum-ℕ = pair-with-sum-ℕ n , is-set-pair-with-sum-ℕ
```

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
    x@((c , p , p+c=n) , a , b , b+a=p) =
      inv
        ( ind-Id
          ( p+c=n)
          ( λ H' H=H' → x ＝ ((c , p , H') , a , b , b+a=p))
          ( refl)
          ( _)
          ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

  is-retraction-map-inv-equiv-pair-with-sum-pr1-pr2 :
    is-retraction
      map-equiv-pair-with-sum-pr1-pr2
      map-inv-equiv-pair-with-sum-pr1-pr2
  is-retraction-map-inv-equiv-pair-with-sum-pr1-pr2
    x@((p , c , c+p=n) , a , b , b+a=p) =
      inv
        ( ind-Id
          ( c+p=n)
          ( λ H' H=H' → x ＝ ((p , c , H') , a , b , b+a=p))
          ( refl)
          ( _)
          ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

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
