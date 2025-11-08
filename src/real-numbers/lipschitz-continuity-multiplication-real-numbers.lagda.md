# Multiplication of real numbers is Lipschitz continuous

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.lipschitz-continuity-multiplication-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.lipschitz-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-closed-intervals-real-numbers
open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.enclosing-closed-rational-intervals-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.inhabited-totally-bounded-subsets-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.uniformly-continuous-functions-real-numbers
```

</details>

## Idea

[Multiplication](real-numbers.multiplication-real-numbers.md) on
[real numbers](real-numbers.dedekind-real-numbers.md) by a constant is a
[Lipschitz function](metric-spaces.lipschitz-functions-metric-spaces.md) from
the [metric space of real numbers](real-numbers.metric-space-of-real-numbers.md)
to itself, specifically implying that it is also
[uniformly continuous](metric-spaces.uniformly-continuous-functions-metric-spaces.md).

## Proof

```agda
module _
  {l1 : Level} (l2 : Level) (c : ℝ l1)
  where

  abstract
    is-lipschitz-right-mul-ℝ :
      is-lipschitz-function-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ c)
    is-lipschitz-right-mul-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open
          do-syntax-trunc-Prop
            ( is-lipschitz-function-prop-Metric-Space
              ( metric-space-ℝ l2)
              ( metric-space-ℝ (l1 ⊔ l2))
              ( mul-ℝ c))
      in do
        (q , |c|<q) ← exists-ℚ⁺-in-upper-cut-ℝ⁰⁺ (nonnegative-abs-ℝ c)
        intro-exists
          ( q)
          ( λ ε x y Nεxy →
            neighborhood-dist-ℝ
              ( q *ℚ⁺ ε)
              ( c *ℝ x)
              ( c *ℝ y)
              ( chain-of-inequalities
                dist-ℝ (c *ℝ x) (c *ℝ y)
                ≤ abs-ℝ c *ℝ dist-ℝ x y
                  by leq-eq-ℝ (inv (left-distributive-abs-mul-dist-ℝ _ _ _))
                ≤ real-ℚ⁺ q *ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-mul-ℝ⁰⁺
                      ( nonnegative-abs-ℝ c)
                      ( nonnegative-real-ℚ⁺ q)
                      ( nonnegative-dist-ℝ x y)
                      ( nonnegative-real-ℚ⁺ ε)
                      ( leq-le-ℝ (le-real-is-in-upper-cut-ℚ (abs-ℝ c) |c|<q))
                      ( leq-dist-neighborhood-ℝ ε x y Nεxy)
                ≤ real-ℚ⁺ (q *ℚ⁺ ε)
                  by leq-eq-ℝ (mul-real-ℚ _ _)))

    is-lipschitz-left-mul-ℝ :
      is-lipschitz-function-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ' c)
    is-lipschitz-left-mul-ℝ =
      is-lipschitz-htpy-function-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ c)
        ( mul-ℝ' c)
        ( commutative-mul-ℝ c)
        ( is-lipschitz-right-mul-ℝ)
```

## Corollaries

### Multiplication is uniformly continuous in each argument

```agda
module _
  {l1 : Level} (l2 : Level) (c : ℝ l1)
  where

  abstract
    is-uniformly-continuous-right-mul-ℝ :
      is-uniformly-continuous-function-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ c)
    is-uniformly-continuous-right-mul-ℝ =
      is-uniformly-continuous-is-lipschitz-function-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ c)
        ( is-lipschitz-right-mul-ℝ l2 c)

    is-uniformly-continuous-left-mul-ℝ :
      is-uniformly-continuous-function-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ' c)
    is-uniformly-continuous-left-mul-ℝ =
      is-uniformly-continuous-is-lipschitz-function-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ' c)
        ( is-lipschitz-left-mul-ℝ l2 c)

  uniformly-continuous-right-mul-ℝ :
    uniformly-continuous-function-ℝ l2 (l1 ⊔ l2)
  uniformly-continuous-right-mul-ℝ =
    ( mul-ℝ c , is-uniformly-continuous-right-mul-ℝ)

  uniformly-continuous-left-mul-ℝ :
    uniformly-continuous-function-ℝ l2 (l1 ⊔ l2)
  uniformly-continuous-left-mul-ℝ =
    ( mul-ℝ' c , is-uniformly-continuous-left-mul-ℝ)
```

### Multiplication is Lipschitz on the Cartesian product of two inhabited totally bounded subsets of ℝ

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : inhabited-totally-bounded-subset-ℝ l1 l2 l3)
  (Y : inhabited-totally-bounded-subset-ℝ l4 l5 l6)
  where

  mul-inhabited-totally-bounded-subset-ℝ :
    type-inhabited-totally-bounded-subset-ℝ X →
    type-inhabited-totally-bounded-subset-ℝ Y →
    ℝ (l2 ⊔ l5)
  mul-inhabited-totally-bounded-subset-ℝ (x , _) (y , _) = x *ℝ y

  abstract
    is-lipschitz-mul-inhabited-totally-bounded-subset-ℝ :
      is-lipschitz-function-Metric-Space
        ( product-Metric-Space
          ( subspace-inhabited-totally-bounded-subset-ℝ X)
          ( subspace-inhabited-totally-bounded-subset-ℝ Y))
        ( metric-space-ℝ (l2 ⊔ l5))
        ( ind-Σ mul-inhabited-totally-bounded-subset-ℝ)
    is-lipschitz-mul-inhabited-totally-bounded-subset-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open
          do-syntax-trunc-Prop
            ( is-lipschitz-function-prop-Metric-Space
              ( product-Metric-Space
                ( subspace-inhabited-totally-bounded-subset-ℝ X)
                ( subspace-inhabited-totally-bounded-subset-ℝ Y))
              ( metric-space-ℝ (l2 ⊔ l5))
              ( ind-Σ mul-inhabited-totally-bounded-subset-ℝ))
      in do
        let
          (mx⁰⁺@(mx , _) , is-max-mx) =
            nonnegative-upper-bound-abs-is-in-inhabited-totally-bounded-subset-ℝ
              ( X)
          (my⁰⁺@(my , _) , is-max-my) =
            nonnegative-upper-bound-abs-is-in-inhabited-totally-bounded-subset-ℝ
              ( Y)
        (q⁺@(q , _) , my+mx<q) ← exists-ℚ⁺-in-upper-cut-ℝ⁰⁺ (my⁰⁺ +ℝ⁰⁺ mx⁰⁺)
        intro-exists
          ( q⁺)
          ( λ ε ((x₁ , _) , (y₁ , y₁∈Y)) ((x₂ , x₂∈X) , (y₂ , _))
              (Nεx₁x₂ , Nεy₁y₂) →
            neighborhood-dist-ℝ
              ( q⁺ *ℚ⁺ ε)
              ( x₁ *ℝ y₁)
              ( x₂ *ℝ y₂)
              ( chain-of-inequalities
                dist-ℝ (x₁ *ℝ y₁) (x₂ *ℝ y₂)
                ≤ dist-ℝ (x₁ *ℝ y₁) (x₂ *ℝ y₁) +ℝ dist-ℝ (x₂ *ℝ y₁) (x₂ *ℝ y₂)
                  by triangle-inequality-dist-ℝ _ _ _
                ≤ dist-ℝ x₁ x₂ *ℝ abs-ℝ y₁ +ℝ abs-ℝ x₂ *ℝ dist-ℝ y₁ y₂
                  by
                    leq-eq-ℝ
                      ( inv
                        ( ap-add-ℝ
                          ( right-distributive-abs-mul-dist-ℝ x₁ x₂ y₁)
                          ( left-distributive-abs-mul-dist-ℝ x₂ y₁ y₂)))
                ≤ real-ℚ⁺ ε *ℝ my +ℝ mx *ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-add-ℝ
                      ( preserves-leq-mul-ℝ⁰⁺
                        ( nonnegative-dist-ℝ x₁ x₂)
                        ( nonnegative-real-ℚ⁺ ε)
                        ( nonnegative-abs-ℝ y₁)
                        ( my⁰⁺)
                        ( leq-dist-neighborhood-ℝ ε x₁ x₂ Nεx₁x₂)
                        ( is-max-my (y₁ , y₁∈Y)))
                      ( preserves-leq-mul-ℝ⁰⁺
                        ( nonnegative-abs-ℝ x₂)
                        ( mx⁰⁺)
                        ( nonnegative-dist-ℝ y₁ y₂)
                        ( nonnegative-real-ℚ⁺ ε)
                        ( is-max-mx (x₂ , x₂∈X))
                        ( leq-dist-neighborhood-ℝ ε y₁ y₂ Nεy₁y₂))
                ≤ my *ℝ real-ℚ⁺ ε +ℝ mx *ℝ real-ℚ⁺ ε
                  by leq-eq-ℝ (ap-add-ℝ (commutative-mul-ℝ _ _) refl)
                ≤ (my +ℝ mx) *ℝ real-ℚ⁺ ε
                  by
                    leq-eq-ℝ
                      ( inv (right-distributive-mul-add-ℝ my mx (real-ℚ⁺ ε)))
                ≤ real-ℚ q *ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-right-mul-ℝ⁰⁺
                      ( nonnegative-real-ℚ⁺ ε)
                      ( leq-le-ℝ (le-real-is-in-upper-cut-ℚ (my +ℝ mx) my+mx<q))
                ≤ real-ℚ⁺ (q⁺ *ℚ⁺ ε)
                  by leq-eq-ℝ (mul-real-ℚ q (rational-ℚ⁺ ε))))

  lipschitz-mul-inhabited-totally-bounded-subset-ℝ :
    lipschitz-function-Metric-Space
      ( product-Metric-Space
        ( subspace-inhabited-totally-bounded-subset-ℝ X)
        ( subspace-inhabited-totally-bounded-subset-ℝ Y))
      ( metric-space-ℝ (l2 ⊔ l5))
  lipschitz-mul-inhabited-totally-bounded-subset-ℝ =
    ( ind-Σ mul-inhabited-totally-bounded-subset-ℝ ,
      is-lipschitz-mul-inhabited-totally-bounded-subset-ℝ)
```

### Multiplication is uniformly continuous on the Cartesian product of two inhabited totally bounded subsets of `ℝ`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : inhabited-totally-bounded-subset-ℝ l1 l2 l3)
  (Y : inhabited-totally-bounded-subset-ℝ l4 l5 l6)
  where

  abstract
    is-uniformly-continuous-mul-inhabited-totally-bounded-subset-ℝ :
      is-uniformly-continuous-function-Metric-Space
        ( product-Metric-Space
          ( subspace-inhabited-totally-bounded-subset-ℝ X)
          ( subspace-inhabited-totally-bounded-subset-ℝ Y))
        ( metric-space-ℝ (l2 ⊔ l5))
        ( ind-Σ (mul-inhabited-totally-bounded-subset-ℝ X Y))
    is-uniformly-continuous-mul-inhabited-totally-bounded-subset-ℝ =
      is-uniformly-continuous-is-lipschitz-function-Metric-Space
        ( product-Metric-Space
          ( subspace-inhabited-totally-bounded-subset-ℝ X)
          ( subspace-inhabited-totally-bounded-subset-ℝ Y))
        ( metric-space-ℝ (l2 ⊔ l5))
        ( ind-Σ (mul-inhabited-totally-bounded-subset-ℝ X Y))
        ( is-lipschitz-mul-inhabited-totally-bounded-subset-ℝ X Y)

  uniformly-continuous-mul-inhabited-totally-bounded-subset-ℝ :
    uniformly-continuous-function-Metric-Space
      ( product-Metric-Space
        ( subspace-inhabited-totally-bounded-subset-ℝ X)
        ( subspace-inhabited-totally-bounded-subset-ℝ Y))
      ( metric-space-ℝ (l2 ⊔ l5))
  uniformly-continuous-mul-inhabited-totally-bounded-subset-ℝ =
    ( ind-Σ (mul-inhabited-totally-bounded-subset-ℝ X Y) ,
      is-uniformly-continuous-mul-inhabited-totally-bounded-subset-ℝ)
```

### Multiplication is not uniformly continuous on `ℝ × ℝ`

This remains to be shown.
