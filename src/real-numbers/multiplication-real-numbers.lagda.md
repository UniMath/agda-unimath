# Multiplication of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.subtypes

open import real-numbers.dedekind-real-numbers
```

</details>

## Definition

```agda

module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  lower-cut-mul-ℝ : subtype (l1 ⊔ l2) ℚ
  lower-cut-mul-ℝ q =
    ∃
      ( type-subtype (rational-bounds-ℝ x))
      ( λ ((a , b) , _) →
        ∃
          ( type-subtype (rational-bounds-ℝ y))
          ( λ ((c , d) , _) →
            le-ℚ-Prop q (a *ℚ c) ∧
            le-ℚ-Prop q (a *ℚ d) ∧
            le-ℚ-Prop q (b *ℚ c) ∧
            le-ℚ-Prop q (b *ℚ d)))

  abstract
    is-inhabited-lower-cut-mul-ℝ : exists ℚ lower-cut-mul-ℝ
    is-inhabited-lower-cut-mul-ℝ =
      do
        ((a , b) , a<x , x<b) ← is-inhabited-rational-bounds-ℝ x
        ((c , d) , c<y , y<d) ← is-inhabited-rational-bounds-ℝ y
        let
          min-ac-ad = min-ℚ (a *ℚ c) (a *ℚ d)
          min-bc-bd = min-ℚ (b *ℚ c) (b *ℚ d)
          min = min-ℚ min-ac-ad min-bc-bd
        (q , q<min) ← exists-lesser-ℚ min
        intro-exists
          ( q)
          ( intro-exists
            ( (a , b) , a<x , x<b)
            ( intro-exists
              ( (c , d) , c<y , y<d)
              ( concatenate-le-leq-ℚ
                  ( q)
                  ( min)
                  ( a *ℚ c)
                  ( q<min)
                  ( transitive-leq-ℚ
                    ( min)
                    ( min-ac-ad)
                    ( a *ℚ c)
                    ( leq-left-min-ℚ (a *ℚ c) (a *ℚ d))
                    ( leq-left-min-ℚ min-ac-ad min-bc-bd)) ,
                concatenate-le-leq-ℚ
                  ( q)
                  ( min)
                  ( a *ℚ d)
                  ( q<min)
                  ( transitive-leq-ℚ
                    ( min)
                    ( min-ac-ad)
                    ( a *ℚ d)
                    ( leq-right-min-ℚ (a *ℚ c) (a *ℚ d))
                    ( leq-left-min-ℚ min-ac-ad min-bc-bd)) ,
                concatenate-le-leq-ℚ
                  ( q)
                  ( min)
                  ( b *ℚ c)
                  ( q<min)
                  ( transitive-leq-ℚ
                    ( min)
                    ( min-bc-bd)
                    ( b *ℚ c)
                    ( leq-left-min-ℚ (b *ℚ c) (b *ℚ d))
                    ( leq-right-min-ℚ min-ac-ad min-bc-bd)) ,
                concatenate-le-leq-ℚ
                  ( q)
                  ( min)
                  ( b *ℚ d)
                  ( q<min)
                  ( transitive-leq-ℚ
                    ( min)
                    ( min-bc-bd)
                    ( b *ℚ d)
                    ( leq-right-min-ℚ (b *ℚ c) (b *ℚ d))
                    ( leq-right-min-ℚ min-ac-ad min-bc-bd)))))
      where open do-syntax-trunc-Prop (∃ ℚ lower-cut-mul-ℝ)
```
