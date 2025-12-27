# Increasing functions on the real numbers

```agda
module real-numbers.increasing-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.subposets

open import real-numbers.addition-real-numbers
open import real-numbers.classically-pointwise-continuous-functions-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A function `f` from the [real numbers](real-numbers.dedekind-real-numbers.md) to
themselves is
{{#concept "increasing" Disambiguation="function from ℝ to ℝ" Agda=is-increasing-function-ℝ}}
if for all `x ≤ y`, `f x ≤ f y`; in other words, it is an
[order-preserving map](order-theory.order-preserving-maps-posets.md) on the
[poset of real numbers](real-numbers.inequality-real-numbers.md).

Several arguments on this page are due to
[Mark Saving](https://math.stackexchange.com/users/798694/mark-saving) in this
Mathematics Stack Exchange answer: <https://math.stackexchange.com/q/5107860>.

## Definition

```agda
is-increasing-prop-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → Prop (lsuc l1 ⊔ l2)
is-increasing-prop-function-ℝ {l1} {l2} =
  preserves-order-prop-Poset (ℝ-Poset l1) (ℝ-Poset l2)

is-increasing-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-increasing-function-ℝ f = type-Prop (is-increasing-prop-function-ℝ f)

is-increasing-on-subset-function-ℝ :
  {l1 l2 l3 : Level} (f : ℝ l1 → ℝ l2) (S : subset-ℝ l3 l1) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
is-increasing-on-subset-function-ℝ f S =
  preserves-order-Poset
    ( poset-Subposet (ℝ-Poset _) S)
    ( ℝ-Poset _)
    ( f ∘ inclusion-subset-ℝ S)
```

## Properties

### If `x < y` implies `f x ≤ f y`, then `f` is increasing

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  abstract
    is-increasing-is-increasing-on-strict-inequalities-ℝ :
      ((x y : ℝ l1) → le-ℝ x y → leq-ℝ (f x) (f y)) →
      is-increasing-function-ℝ f
    is-increasing-is-increasing-on-strict-inequalities-ℝ H x y x≤y =
      double-negation-elim-leq-ℝ
        ( f x)
        ( f y)
        ( map-double-negation
          ( rec-coproduct
            ( λ x~y → leq-eq-ℝ (ap f (eq-sim-ℝ x~y)))
            ( H x y))
          ( irrefutable-sim-or-le-leq-ℝ x y x≤y))

module _
  {l1 l2 l3 : Level}
  (f : ℝ l1 → ℝ l2)
  (S : subset-ℝ l3 l1)
  where

  abstract
    is-increasing-is-increasing-on-strict-inequalities-on-subset-function-ℝ :
      ( ((x y : type-subset-ℝ S) →
        le-ℝ (pr1 x) (pr1 y) → leq-ℝ (f (pr1 x)) (f (pr1 y)))) →
      is-increasing-on-subset-function-ℝ f S
    is-increasing-is-increasing-on-strict-inequalities-on-subset-function-ℝ
      H (x , x∈S) (y , y∈S) x≤y =
      double-negation-elim-leq-ℝ
        ( f x)
        ( f y)
        ( map-double-negation
          ( rec-coproduct
            ( λ x~y → leq-eq-ℝ (ap f (eq-sim-ℝ x~y)))
            ( H (x , x∈S) (y , y∈S)))
          ( irrefutable-sim-or-le-leq-ℝ x y x≤y))
```

### If a pointwise continuous function `f` is increasing on a dense subset of `ℝ`, then it is increasing on `ℝ`

```agda
module _
  {l1 l2 l3 : Level}
  (f : pointwise-continuous-map-ℝ l1 l2)
  (S : dense-subset-ℝ l3 l1)
  where

  abstract
    is-increasing-is-increasing-dense-subset-pointwise-continuous-map-ℝ :
      is-increasing-on-subset-function-ℝ
        ( map-pointwise-continuous-map-ℝ f)
        ( subset-dense-subset-ℝ S) →
      is-increasing-function-ℝ (map-pointwise-continuous-map-ℝ f)
    is-increasing-is-increasing-dense-subset-pointwise-continuous-map-ℝ H =
      let
        f' = map-pointwise-continuous-map-ℝ f
        open do-syntax-trunc-Prop empty-Prop
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        is-increasing-is-increasing-on-strict-inequalities-ℝ
          ( map-pointwise-continuous-map-ℝ f)
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
                    is-classically-pointwise-continuous-pointwise-continuous-map-ℝ
                      ( f)
                      ( x)
                      ( εx)
                  (δy , Hδy) ←
                    is-classically-pointwise-continuous-pointwise-continuous-map-ℝ
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
  (f : pointwise-continuous-map-ℝ l1 l2)
  where

  abstract
    is-increasing-is-increasing-rational-ℝ :
      preserves-order-Poset
        ( ℚ-Poset)
        ( ℝ-Poset l2)
        ( map-pointwise-continuous-map-ℝ f ∘ raise-real-ℚ l1) →
      is-increasing-function-ℝ (map-pointwise-continuous-map-ℝ f)
    is-increasing-is-increasing-rational-ℝ H =
      is-increasing-is-increasing-dense-subset-pointwise-continuous-map-ℝ
        ( f)
        ( dense-subset-rational-ℝ l1)
        ( λ (x , p , x~p) (y , q , y~q) x≤y →
          binary-tr
            ( leq-ℝ)
            ( ap
              ( map-pointwise-continuous-map-ℝ f)
              ( inv (eq-raise-real-rational-is-rational-ℝ x~p)))
            ( ap
              ( map-pointwise-continuous-map-ℝ f)
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
