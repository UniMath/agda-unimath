# Multiplication of real numbers is Lipschitz continuous

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.lipschitz-continuity-multiplication-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.square-roots-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.continuity-of-maps-at-points-metric-spaces
open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.pointwise-continuous-maps-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.inhabited-totally-bounded-subsets-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.saturation-inequality-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.uniformly-continuous-endomaps-real-numbers
```

</details>

## Idea

[Multiplication](real-numbers.multiplication-real-numbers.md) on
[real numbers](real-numbers.dedekind-real-numbers.md) by a constant is a
[Lipschitz function](metric-spaces.lipschitz-maps-metric-spaces.md) from the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md) to
itself, specifically implying that it is also
[uniformly continuous](metric-spaces.uniformly-continuous-maps-metric-spaces.md).

## Proof

```agda
module _
  {l1 : Level} (l2 : Level) (c : ℝ l1)
  where

  abstract
    is-lipschitz-map-right-mul-ℝ :
      is-lipschitz-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ c)
    is-lipschitz-map-right-mul-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open
          do-syntax-trunc-Prop
            ( is-lipschitz-prop-map-Metric-Space
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
                      ( leq-le-ℝ (le-real-is-in-upper-cut-ℝ (abs-ℝ c) |c|<q))
                      ( leq-dist-neighborhood-ℝ ε x y Nεxy)
                ≤ real-ℚ⁺ (q *ℚ⁺ ε)
                  by leq-eq-ℝ (mul-real-ℚ _ _)))

    is-lipschitz-map-left-mul-ℝ :
      is-lipschitz-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ' c)
    is-lipschitz-map-left-mul-ℝ =
      is-lipschitz-htpy-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ c)
        ( mul-ℝ' c)
        ( commutative-mul-ℝ c)
        ( is-lipschitz-map-right-mul-ℝ)
```

## Corollaries

### Multiplication is uniformly continuous in each argument

```agda
module _
  {l1 : Level} (l2 : Level) (c : ℝ l1)
  where

  abstract
    is-uniformly-continuous-map-right-mul-ℝ :
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ c)
    is-uniformly-continuous-map-right-mul-ℝ =
      is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ c)
        ( is-lipschitz-map-right-mul-ℝ l2 c)

    is-uniformly-continuous-map-left-mul-ℝ :
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ' c)
    is-uniformly-continuous-map-left-mul-ℝ =
      is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-ℝ' c)
        ( is-lipschitz-map-left-mul-ℝ l2 c)

  uniformly-continuous-map-right-mul-ℝ :
    uniformly-continuous-endomap-ℝ l2 (l1 ⊔ l2)
  uniformly-continuous-map-right-mul-ℝ =
    ( mul-ℝ c , is-uniformly-continuous-map-right-mul-ℝ)

  uniformly-continuous-map-left-mul-ℝ :
    uniformly-continuous-endomap-ℝ l2 (l1 ⊔ l2)
  uniformly-continuous-map-left-mul-ℝ =
    ( mul-ℝ' c , is-uniformly-continuous-map-left-mul-ℝ)
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

  mul-pair-inhabited-totally-bounded-subset-ℝ :
    type-inhabited-totally-bounded-subset-ℝ X ×
    type-inhabited-totally-bounded-subset-ℝ Y →
    ℝ (l2 ⊔ l5)
  mul-pair-inhabited-totally-bounded-subset-ℝ =
    rec-product mul-inhabited-totally-bounded-subset-ℝ

  abstract
    is-lipschitz-map-mul-pair-inhabited-totally-bounded-subset-ℝ :
      is-lipschitz-map-Metric-Space
        ( product-Metric-Space
          ( subspace-inhabited-totally-bounded-subset-ℝ X)
          ( subspace-inhabited-totally-bounded-subset-ℝ Y))
        ( metric-space-ℝ (l2 ⊔ l5))
        ( mul-pair-inhabited-totally-bounded-subset-ℝ)
    is-lipschitz-map-mul-pair-inhabited-totally-bounded-subset-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open
          do-syntax-trunc-Prop
            ( is-lipschitz-prop-map-Metric-Space
              ( product-Metric-Space
                ( subspace-inhabited-totally-bounded-subset-ℝ X)
                ( subspace-inhabited-totally-bounded-subset-ℝ Y))
              ( metric-space-ℝ (l2 ⊔ l5))
              ( mul-pair-inhabited-totally-bounded-subset-ℝ))
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
                      ( leq-le-ℝ (le-real-is-in-upper-cut-ℝ (my +ℝ mx) my+mx<q))
                ≤ real-ℚ⁺ (q⁺ *ℚ⁺ ε)
                  by leq-eq-ℝ (mul-real-ℚ q (rational-ℚ⁺ ε))))

  lipschitz-map-mul-pair-inhabited-totally-bounded-subset-ℝ :
    lipschitz-map-Metric-Space
      ( product-Metric-Space
        ( subspace-inhabited-totally-bounded-subset-ℝ X)
        ( subspace-inhabited-totally-bounded-subset-ℝ Y))
      ( metric-space-ℝ (l2 ⊔ l5))
  lipschitz-map-mul-pair-inhabited-totally-bounded-subset-ℝ =
    ( mul-pair-inhabited-totally-bounded-subset-ℝ ,
      is-lipschitz-map-mul-pair-inhabited-totally-bounded-subset-ℝ)
```

### Multiplication is uniformly continuous on the Cartesian product of two inhabited totally bounded subsets of `ℝ`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : inhabited-totally-bounded-subset-ℝ l1 l2 l3)
  (Y : inhabited-totally-bounded-subset-ℝ l4 l5 l6)
  where

  abstract
    is-uniformly-continuous-map-mul-pair-inhabited-totally-bounded-subset-ℝ :
      is-uniformly-continuous-map-Metric-Space
        ( product-Metric-Space
          ( subspace-inhabited-totally-bounded-subset-ℝ X)
          ( subspace-inhabited-totally-bounded-subset-ℝ Y))
        ( metric-space-ℝ (l2 ⊔ l5))
        ( mul-pair-inhabited-totally-bounded-subset-ℝ X Y)
    is-uniformly-continuous-map-mul-pair-inhabited-totally-bounded-subset-ℝ =
      is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
        ( product-Metric-Space
          ( subspace-inhabited-totally-bounded-subset-ℝ X)
          ( subspace-inhabited-totally-bounded-subset-ℝ Y))
        ( metric-space-ℝ (l2 ⊔ l5))
        ( rec-product (mul-inhabited-totally-bounded-subset-ℝ X Y))
        ( is-lipschitz-map-mul-pair-inhabited-totally-bounded-subset-ℝ X Y)

  uniformly-continuous-map-mul-pair-inhabited-totally-bounded-subset-ℝ :
    uniformly-continuous-map-Metric-Space
      ( product-Metric-Space
        ( subspace-inhabited-totally-bounded-subset-ℝ X)
        ( subspace-inhabited-totally-bounded-subset-ℝ Y))
      ( metric-space-ℝ (l2 ⊔ l5))
  uniformly-continuous-map-mul-pair-inhabited-totally-bounded-subset-ℝ =
    ( mul-pair-inhabited-totally-bounded-subset-ℝ X Y ,
      is-uniformly-continuous-map-mul-pair-inhabited-totally-bounded-subset-ℝ)
```

### Multiplication is not uniformly continuous on `ℝ × ℝ`

This remains to be shown.

### Multiplication is pointwise continuous on `ℝ × ℝ`

```agda
module _
  (l1 l2 : Level)
  where

  abstract
    is-pointwise-continuous-map-mul-pair-ℝ :
      is-pointwise-continuous-map-Metric-Space
        ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
        ( metric-space-ℝ (l1 ⊔ l2))
        ( mul-pair-ℝ)
    is-pointwise-continuous-map-mul-pair-ℝ (x , y) =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open
          do-syntax-trunc-Prop
            ( is-continuous-at-point-prop-map-Metric-Space
              ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
              ( metric-space-ℝ (l1 ⊔ l2))
              ( mul-pair-ℝ)
              ( x , y))
      in do
        (q⁺ , |x|+|y|<q) ←
          exists-ℚ⁺-in-upper-cut-ℝ⁰⁺
            ( nonnegative-abs-ℝ x +ℝ⁰⁺ nonnegative-abs-ℝ y)
        let
          modulus :
            (ε : ℚ⁺) →
            Σ ( ℚ⁺)
              ( λ δ →
                (x' : ℝ l1) (y' : ℝ l2) →
                neighborhood-ℝ l1 δ x x' → neighborhood-ℝ l2 δ y y' →
                neighborhood-ℝ (l1 ⊔ l2) ε (x *ℝ y) (x' *ℝ y'))
          modulus ε =
            let
              (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε
              δ₁ = inv-ℚ⁺ q⁺ *ℚ⁺ ε₁
              (δ₂ , δ₂²<ε₂) = bound-square-le-ℚ⁺ ε₂
              δ = min-ℚ⁺ δ₁ δ₂
            in
              ( δ ,
                λ x' y' Nδxx' Nδyy' →
                  let
                    dx = x' -ℝ x
                    dy = y' -ℝ y
                    |dx|≤δ =
                      leq-dist-neighborhood-ℝ δ _ _
                        ( is-symmetric-neighborhood-ℝ δ _ _ Nδxx')
                    |dy|≤δ =
                      leq-dist-neighborhood-ℝ δ _ _
                        ( is-symmetric-neighborhood-ℝ δ _ _ Nδyy')
                  in
                    neighborhood-dist-ℝ _ _ _
                      ( chain-of-inequalities
                        dist-ℝ (x *ℝ y) (x' *ℝ y')
                        ≤ dist-ℝ (x *ℝ y) ((x +ℝ dx) *ℝ (y +ℝ dy))
                          by
                            leq-eq-ℝ
                              ( ap-binary
                                ( λ a b → dist-ℝ (x *ℝ y) (a *ℝ b))
                                ( inv
                                  ( eq-sim-ℝ
                                    ( cancel-right-conjugation-ℝ x x')))
                                ( inv
                                  ( eq-sim-ℝ
                                    ( cancel-right-conjugation-ℝ y y'))))
                        ≤ dist-ℝ
                            ( x *ℝ y)
                            ( x *ℝ (y +ℝ dy) +ℝ dx *ℝ (y +ℝ dy))
                          by
                            leq-eq-ℝ
                              ( ap
                                ( dist-ℝ _)
                                ( right-distributive-mul-add-ℝ _ _ _))
                        ≤ dist-ℝ
                            ( x *ℝ y)
                            ( ((x *ℝ y) +ℝ (x *ℝ dy)) +ℝ (dx *ℝ y +ℝ dx *ℝ dy))
                          by
                            leq-eq-ℝ
                              ( ap
                                ( dist-ℝ _)
                                ( ap-add-ℝ
                                  ( left-distributive-mul-add-ℝ _ _ _)
                                  ( left-distributive-mul-add-ℝ _ _ _)))
                        ≤ dist-ℝ
                            ( x *ℝ y)
                            ( (x *ℝ y) +ℝ (x *ℝ dy +ℝ (dx *ℝ y +ℝ dx *ℝ dy)))
                          by leq-eq-ℝ (ap (dist-ℝ _) (associative-add-ℝ _ _ _))
                        ≤ abs-ℝ (x *ℝ dy +ℝ (dx *ℝ y +ℝ dx *ℝ dy))
                          by leq-sim-ℝ (dist-right-add-ℝ _ _)
                        ≤ abs-ℝ (x *ℝ dy) +ℝ abs-ℝ (dx *ℝ y +ℝ dx *ℝ dy)
                          by triangle-inequality-abs-ℝ _ _
                        ≤ ( abs-ℝ x *ℝ abs-ℝ dy) +ℝ
                          ( abs-ℝ (dx *ℝ y) +ℝ abs-ℝ (dx *ℝ dy))
                          by
                            preserves-leq-add-ℝ
                              ( leq-eq-ℝ (abs-mul-ℝ _ _))
                              ( triangle-inequality-abs-ℝ _ _)
                        ≤ ( abs-ℝ x *ℝ real-ℚ⁺ δ₁) +ℝ
                          ( abs-ℝ dx *ℝ abs-ℝ y +ℝ abs-ℝ dx *ℝ abs-ℝ dy)
                          by
                            preserves-leq-add-ℝ
                              ( preserves-leq-left-mul-ℝ⁰⁺
                                ( nonnegative-abs-ℝ x)
                                ( transitive-leq-ℝ _ _ _
                                  ( preserves-leq-real-ℚ (leq-left-min-ℚ _ _))
                                  ( |dy|≤δ)))
                              ( leq-eq-ℝ
                                ( ap-add-ℝ (abs-mul-ℝ _ _) (abs-mul-ℝ _ _)))
                        ≤ ( real-ℚ⁺ δ₁ *ℝ abs-ℝ x) +ℝ
                          ( real-ℚ⁺ δ₁ *ℝ abs-ℝ y +ℝ real-ℚ⁺ δ₂ *ℝ real-ℚ⁺ δ₂)
                          by
                            preserves-leq-add-ℝ
                              ( leq-eq-ℝ (commutative-mul-ℝ _ _))
                              ( preserves-leq-add-ℝ
                                ( preserves-leq-right-mul-ℝ⁰⁺
                                  ( nonnegative-abs-ℝ y)
                                  ( transitive-leq-ℝ _ _ _
                                    ( preserves-leq-real-ℚ (leq-left-min-ℚ _ _))
                                    ( |dx|≤δ)))
                                ( preserves-leq-mul-ℝ⁰⁺
                                  ( nonnegative-abs-ℝ dx)
                                  ( nonnegative-real-ℚ⁺ δ₂)
                                  ( nonnegative-abs-ℝ dy)
                                  ( nonnegative-real-ℚ⁺ δ₂)
                                  ( transitive-leq-ℝ _ _ _
                                    ( preserves-leq-real-ℚ
                                      ( leq-right-min-ℚ _ _))
                                    ( |dx|≤δ))
                                  ( transitive-leq-ℝ _ _ _
                                    ( preserves-leq-real-ℚ
                                      ( leq-right-min-ℚ _ _))
                                    ( |dy|≤δ))))
                        ≤ ( real-ℚ⁺ δ₁ *ℝ abs-ℝ x +ℝ real-ℚ⁺ δ₁ *ℝ abs-ℝ y) +ℝ
                          ( real-ℚ⁺ δ₂ *ℝ real-ℚ⁺ δ₂)
                          by leq-eq-ℝ (inv (associative-add-ℝ _ _ _))
                        ≤ ( real-ℚ⁺ δ₁ *ℝ (abs-ℝ x +ℝ abs-ℝ y)) +ℝ
                          ( real-ℚ⁺ (δ₂ *ℚ⁺ δ₂))
                          by
                            leq-eq-ℝ
                              ( ap-add-ℝ
                                ( inv (left-distributive-mul-add-ℝ _ _ _))
                                ( mul-real-ℚ _ _))
                        ≤ ( real-ℚ⁺ (inv-ℚ⁺ q⁺ *ℚ⁺ ε₁) *ℝ real-ℚ⁺ q⁺) +ℝ
                          ( real-ℚ⁺ ε₂)
                          by
                            preserves-leq-add-ℝ
                              ( preserves-leq-left-mul-ℝ⁰⁺
                                ( nonnegative-real-ℚ⁺ (inv-ℚ⁺ q⁺ *ℚ⁺ ε₁))
                                ( leq-real-is-in-upper-cut-ℝ _ |x|+|y|<q))
                              ( preserves-leq-real-ℚ (leq-le-ℚ δ₂²<ε₂))
                        ≤ ( real-ℚ⁺ ((inv-ℚ⁺ q⁺ *ℚ⁺ ε₁) *ℚ⁺ q⁺)) +ℝ
                          ( real-ℚ⁺ ε₂)
                          by leq-eq-ℝ (ap-add-ℝ (mul-real-ℚ _ _) refl)
                        ≤ ( real-ℚ⁺ ((ε₁ *ℚ⁺ inv-ℚ⁺ q⁺) *ℚ⁺ q⁺)) +ℝ
                          ( real-ℚ⁺ ε₂)
                          by
                            leq-eq-ℝ
                              ( ap-add-ℝ
                                ( ap real-ℚ⁺
                                  ( ap-mul-ℚ⁺ (commutative-mul-ℚ⁺ _ _) refl))
                                ( refl))
                        ≤ real-ℚ⁺ ε₁ +ℝ real-ℚ⁺ ε₂
                          by
                            leq-eq-ℝ
                              ( ap-add-ℝ
                                ( ap
                                  ( real-ℚ⁺)
                                  ( eq-ℚ⁺ (is-section-right-div-ℚ⁺ q⁺ _)))
                                ( refl))
                        ≤ real-ℚ⁺ (ε₁ +ℚ⁺ ε₂)
                          by leq-eq-ℝ (add-real-ℚ _ _)
                        ≤ real-ℚ⁺ ε
                          by leq-eq-ℝ (ap real-ℚ⁺ ε₁+ε₂=ε)))
        intro-exists
          ( pr1 ∘ modulus)
          ( λ ε (x' , y') (Nδxx' , Nδyy') → pr2 (modulus ε) x' y' Nδxx' Nδyy')

  pointwise-continuous-map-mul-pair-ℝ :
    pointwise-continuous-map-Metric-Space
      ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
      ( metric-space-ℝ (l1 ⊔ l2))
  pointwise-continuous-map-mul-pair-ℝ =
    ( mul-pair-ℝ ,
      is-pointwise-continuous-map-mul-pair-ℝ)
```

### Given nonnegative real numbers `x`, `y`, `z`, if `x ≤ (y + δ)(z + ε)` for all positive `δ` and `ε`, then `x ≤ yz`

```agda
abstract
  saturated-leq-mul-ℝ⁰⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3) →
    ( (δ ε : ℚ⁺) →
      leq-ℝ⁰⁺
        ( x)
        ((y +ℝ⁰⁺ nonnegative-real-ℚ⁺ δ) *ℝ⁰⁺ (z +ℝ⁰⁺ nonnegative-real-ℚ⁺ ε))) →
    leq-ℝ⁰⁺ x (y *ℝ⁰⁺ z)
  saturated-leq-mul-ℝ⁰⁺ x⁰⁺@(x , _) y⁰⁺@(y , _) z⁰⁺@(z , _) H =
    saturated-leq-ℝ
      ( x)
      ( y *ℝ z)
      ( λ η →
        let
          open inequality-reasoning-Large-Poset ℝ-Large-Poset
          open do-syntax-trunc-Prop (leq-prop-ℝ x (y *ℝ z +ℝ real-ℚ⁺ η))
        in do
          (μ , is-mod-μ) ← is-pointwise-continuous-map-mul-pair-ℝ _ _ (y , z)
          let δ = μ η
          chain-of-inequalities
            x
            ≤ (y +ℝ real-ℚ⁺ δ) *ℝ (z +ℝ real-ℚ⁺ δ)
              by H δ δ
            ≤ ( abs-ℝ (y *ℝ z)) +ℝ
              ( dist-ℝ (y *ℝ z) ((y +ℝ real-ℚ⁺ δ) *ℝ (z +ℝ real-ℚ⁺ δ)))
              by leq-add-abs-dist-ℝ _ _
            ≤ ( y *ℝ z) +ℝ
              ( dist-ℝ (y *ℝ z) ((y +ℝ real-ℚ⁺ δ) *ℝ (z +ℝ real-ℚ⁺ δ)))
              by leq-eq-ℝ (ap-add-ℝ (abs-real-ℝ⁰⁺ (y⁰⁺ *ℝ⁰⁺ z⁰⁺)) refl)
            ≤ y *ℝ z +ℝ real-ℚ⁺ η
              by
                preserves-leq-left-add-ℝ _ _ _
                  ( leq-dist-neighborhood-ℝ
                    ( η)
                    ( _)
                    ( _)
                    ( is-mod-μ
                      ( η)
                      ( y +ℝ real-ℚ⁺ δ , z +ℝ real-ℚ⁺ δ)
                      ( neighborhood-right-add-real-ℚ⁺ y δ ,
                        neighborhood-right-add-real-ℚ⁺ z δ))))

  saturated-leq-left-mul-ℝ⁰⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3) →
    ((ε : ℚ⁺) → leq-ℝ⁰⁺ x (y *ℝ⁰⁺ (z +ℝ⁰⁺ nonnegative-real-ℚ⁺ ε))) →
    leq-ℝ⁰⁺ x (y *ℝ⁰⁺ z)
  saturated-leq-left-mul-ℝ⁰⁺ x y z H =
    saturated-leq-mul-ℝ⁰⁺ x y z
      ( λ δ ε →
        transitive-leq-ℝ _ _ _
          ( preserves-leq-right-mul-ℝ⁰⁺
            ( z +ℝ⁰⁺ nonnegative-real-ℚ⁺ ε)
            ( leq-left-add-real-ℝ⁰⁺ (real-ℝ⁰⁺ y) (nonnegative-real-ℚ⁺ δ)))
          ( H ε))
```
