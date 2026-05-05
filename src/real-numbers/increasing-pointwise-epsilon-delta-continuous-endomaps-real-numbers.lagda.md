# Increasing pointwise ε-δ continuous endomaps on the real numbers

```agda
module real-numbers.increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.order-preserving-maps-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.increasing-endomaps-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

This page describes the interaction of
[pointwise ε-δ continuity of endomaps of real numbers](real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers.md)
and being [increasing](real-numbers.increasing-endomaps-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (f : pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  where

  is-increasing-prop-pointwise-ε-δ-continuous-endomap-ℝ : Prop (lsuc l1 ⊔ l2)
  is-increasing-prop-pointwise-ε-δ-continuous-endomap-ℝ =
    is-increasing-prop-endomap-ℝ (map-pointwise-ε-δ-continuous-endomap-ℝ f)

  is-increasing-pointwise-ε-δ-continuous-endomap-ℝ : UU (lsuc l1 ⊔ l2)
  is-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    type-Prop is-increasing-prop-pointwise-ε-δ-continuous-endomap-ℝ

increasing-pointwise-ε-δ-continuous-endomap-ℝ :
  (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
increasing-pointwise-ε-δ-continuous-endomap-ℝ l1 l2 =
  type-subtype (is-increasing-prop-pointwise-ε-δ-continuous-endomap-ℝ {l1} {l2})

module _
  {l1 l2 : Level}
  (f : increasing-pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  where

  pointwise-ε-δ-continuous-endomap-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    pointwise-ε-δ-continuous-endomap-ℝ l1 l2
  pointwise-ε-δ-continuous-endomap-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    pr1 f

  map-increasing-pointwise-ε-δ-continuous-endomap-ℝ : ℝ l1 → ℝ l2
  map-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    map-pointwise-ε-δ-continuous-endomap-ℝ
      ( pointwise-ε-δ-continuous-endomap-increasing-pointwise-ε-δ-continuous-endomap-ℝ)

  is-increasing-map-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-increasing-endomap-ℝ map-increasing-pointwise-ε-δ-continuous-endomap-ℝ
  is-increasing-map-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    pr2 f

  is-pointwise-ε-δ-continuous-map-increasing-pointwise-ε-δ-continuous-endomap-ℝ :
    is-pointwise-ε-δ-continuous-endomap-ℝ
      ( map-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
  is-pointwise-ε-δ-continuous-map-increasing-pointwise-ε-δ-continuous-endomap-ℝ =
    is-pointwise-ε-δ-continuous-map-pointwise-ε-δ-continuous-endomap-ℝ
      ( pointwise-ε-δ-continuous-endomap-increasing-pointwise-ε-δ-continuous-endomap-ℝ)
```

## Properties

### If a pointwise ε-δ continuous function `f` is increasing on a dense subset of `ℝ`, then it is increasing on `ℝ`

```agda
module _
  {l1 l2 l3 : Level}
  (f : pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  (S : dense-subset-ℝ l3 l1)
  where

  abstract
    is-increasing-is-increasing-dense-subset-pointwise-ε-δ-continuous-endomap-ℝ :
      is-increasing-on-subset-endomap-ℝ
        ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
        ( subset-dense-subset-ℝ S) →
      is-increasing-endomap-ℝ (map-pointwise-ε-δ-continuous-endomap-ℝ f)
    is-increasing-is-increasing-dense-subset-pointwise-ε-δ-continuous-endomap-ℝ
      H =
      let
        f' = map-pointwise-ε-δ-continuous-endomap-ℝ f
        open do-syntax-trunc-Prop empty-Prop
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        is-increasing-is-increasing-on-strict-inequalities-endomap-ℝ
          ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
          ( λ x y x<y →
            leq-not-le-ℝ
              ( f' y)
              ( f' x)
              ( λ f'y<f'x →
                do
                  (ε , f'y+ε<f'x) ←
                    exists-positive-rational-separation-le-ℝ f'y<f'x
                  let (εx , εy , εx+εy=ε) = split-ℚ⁺ ε
                  (δx , Hδx) ←
                    is-pointwise-ε-δ-continuous-map-pointwise-ε-δ-continuous-endomap-ℝ
                      ( f)
                      ( x)
                      ( εx)
                  (δy , Hδy) ←
                    is-pointwise-ε-δ-continuous-map-pointwise-ε-δ-continuous-endomap-ℝ
                      ( f)
                      ( y)
                      ( εy)
                  ( ( (x' , x'∈S) , (y' , y'∈S)) , x'<y' , Nxx' , Nyy') ←
                    exist-close-le-elements-dense-subset-ℝ S δx δy x<y
                  not-leq-le-ℝ _ _
                    ( f'y+ε<f'x)
                    ( chain-of-inequalities
                      f' x
                      ≤ f' x' +ℝ real-ℚ⁺ εx
                        by
                          left-leq-real-bound-neighborhood-ℝ
                            ( εx)
                            ( f' x)
                            ( f' x')
                            ( Hδx x' Nxx')
                      ≤ f' y' +ℝ real-ℚ⁺ εx
                        by
                          preserves-leq-right-add-ℝ
                            ( real-ℚ⁺ εx)
                            ( f' x')
                            ( f' y')
                            ( H (x' , x'∈S) (y' , y'∈S) (leq-le-ℝ x'<y'))
                      ≤ (f' y +ℝ real-ℚ⁺ εy) +ℝ real-ℚ⁺ εx
                        by
                          preserves-leq-right-add-ℝ
                            ( real-ℚ⁺ εx)
                            ( f' y')
                            ( f' y +ℝ real-ℚ⁺ εy)
                            ( right-leq-real-bound-neighborhood-ℝ
                              ( εy)
                              ( f' y)
                              ( f' y')
                              ( Hδy y' Nyy'))
                      ≤ f' y +ℝ real-ℚ⁺ ε
                        by
                          leq-eq-ℝ
                            ( equational-reasoning
                              f' y +ℝ real-ℚ⁺ εy +ℝ real-ℚ⁺ εx
                              ＝ f' y +ℝ (real-ℚ⁺ εy +ℝ real-ℚ⁺ εx)
                                by associative-add-ℝ _ _ _
                              ＝ f' y +ℝ real-ℚ⁺ (εy +ℚ⁺ εx)
                                by ap-add-ℝ refl (add-real-ℚ _ _)
                              ＝ f' y +ℝ real-ℚ⁺ ε
                                by
                                  ap-add-ℝ
                                    ( refl)
                                    ( ap
                                      ( real-ℚ⁺)
                                      ( commutative-add-ℚ⁺ εy εx ∙ εx+εy=ε))))))
```

### If `f` is pointwise continuous and increasing on the rational real numbers, it is increasing on the real numbers

```agda
module _
  {l1 l2 : Level}
  (f : pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  where

  abstract
    is-increasing-is-increasing-rational-pointwise-ε-δ-continuous-endomap-ℝ :
      preserves-order-Poset
        ( ℚ-Poset)
        ( ℝ-Poset l2)
        ( map-pointwise-ε-δ-continuous-endomap-ℝ f ∘ raise-real-ℚ l1) →
      is-increasing-endomap-ℝ (map-pointwise-ε-δ-continuous-endomap-ℝ f)
    is-increasing-is-increasing-rational-pointwise-ε-δ-continuous-endomap-ℝ H =
      is-increasing-is-increasing-dense-subset-pointwise-ε-δ-continuous-endomap-ℝ
        ( f)
        ( dense-subset-rational-ℝ l1)
        ( λ (x , p , x~p) (y , q , y~q) x≤y →
          binary-tr
            ( leq-ℝ)
            ( ap
              ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
              ( inv (eq-raise-real-rational-is-rational-ℝ x~p)))
            ( ap
              ( map-pointwise-ε-δ-continuous-endomap-ℝ f)
              ( inv (eq-raise-real-rational-is-rational-ℝ y~q)))
            ( H
              ( p)
              ( q)
              ( reflects-leq-real-ℚ
                ( leq-leq-raise-ℝ l1
                  ( binary-tr
                    ( leq-ℝ)
                    ( eq-raise-real-rational-is-rational-ℝ x~p)
                    ( eq-raise-real-rational-is-rational-ℝ y~q)
                    ( x≤y))))))
```
