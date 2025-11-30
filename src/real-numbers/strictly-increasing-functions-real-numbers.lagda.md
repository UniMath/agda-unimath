# Strictly increasing functions on the real numbers

```agda
module real-numbers.strictly-increasing-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.increasing-functions-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A function `f` from the [real numbers](real-numbers.dedekind-real-numbers.md) to
themselves is
{{#concept "strictly increasing" WDID=Q78055984 WD="strictly increasing function" Disambiguation="function from ℝ to ℝ" Agda=is-strictly-increasing-function-ℝ}}
if for all `x < y`, `f x < f y`.

Several arguments on this page are due to
[Mark Saving](https://math.stackexchange.com/users/798694/mark-saving) in this
Mathematics Stack Exchange answer: <https://math.stackexchange.com/q/5107860>.

## Definition

```agda
is-strictly-increasing-prop-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → Prop (lsuc l1 ⊔ l2)
is-strictly-increasing-prop-function-ℝ {l1} {l2} f =
  Π-Prop
    ( ℝ l1)
    ( λ x →
      Π-Prop
        ( ℝ l1)
        ( λ y → le-prop-ℝ x y ⇒ le-prop-ℝ (f x) (f y)))

is-strictly-increasing-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-strictly-increasing-function-ℝ f =
  type-Prop (is-strictly-increasing-prop-function-ℝ f)

is-strictly-increasing-on-subset-function-ℝ :
  {l1 l2 l3 : Level} → (ℝ l1 → ℝ l2) → subset-ℝ l3 l1 → UU (lsuc l1 ⊔ l2 ⊔ l3)
is-strictly-increasing-on-subset-function-ℝ f S =
  (x y : type-subset-ℝ S) → le-ℝ (pr1 x) (pr1 y) → le-ℝ (f (pr1 x)) (f (pr1 y))
```

## Properties

### A strictly increasing function is increasing

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  abstract
    is-increasing-is-strictly-increasing-function-ℝ :
      is-strictly-increasing-function-ℝ f → is-increasing-function-ℝ f
    is-increasing-is-strictly-increasing-function-ℝ H =
      strengthen-is-increasing-function-ℝ f (λ x y x<y → leq-le-ℝ (H x y x<y))
```

### If a pointwise continuous function is strictly increasing on a dense subset of ℝ, then it is strictly increasing on ℝ

```agda
module _
  {l1 l2 l3 : Level}
  (f : pointwise-continuous-function-ℝ l1 l2)
  (S : dense-subset-ℝ l3 l1)
  where

  abstract
    is-strictly-increasing-is-strictly-increasing-dense-subset-pointwise-continuous-function-ℝ :
      is-strictly-increasing-on-subset-function-ℝ
        ( map-pointwise-continuous-function-ℝ f)
        ( subset-dense-subset-ℝ S) →
      is-strictly-increasing-function-ℝ (map-pointwise-continuous-function-ℝ f)
    is-strictly-increasing-is-strictly-increasing-dense-subset-pointwise-continuous-function-ℝ
      H x y x<y =
      let
        H' =
          is-increasing-is-increasing-dense-subset-pointwise-continuous-function-ℝ
            ( f)
            ( S)
            ( strengthen-is-increasing-on-subset-function-ℝ
              ( map-pointwise-continuous-function-ℝ f)
              ( subset-dense-subset-ℝ S)
              ( λ a b a<b → leq-le-ℝ (H a b a<b)))
        open
          do-syntax-trunc-Prop
            ( le-prop-ℝ
              ( map-pointwise-continuous-function-ℝ f x)
              ( map-pointwise-continuous-function-ℝ f y))
      in do
        (a , a∈S , x<a , a<y) ← dense-le-dense-subset-ℝ S x<y
        (b , b∈S , a<b , b<y) ← dense-le-dense-subset-ℝ S a<y
        concatenate-leq-le-ℝ
          ( map-pointwise-continuous-function-ℝ f x)
          ( map-pointwise-continuous-function-ℝ f a)
          ( map-pointwise-continuous-function-ℝ f y)
          ( H' x a (leq-le-ℝ x<a))
          ( concatenate-le-leq-ℝ
            ( map-pointwise-continuous-function-ℝ f a)
            ( map-pointwise-continuous-function-ℝ f b)
            ( map-pointwise-continuous-function-ℝ f y)
            ( H (a , a∈S) (b , b∈S) a<b)
            ( H' b y (leq-le-ℝ b<y)))
```

### If `f` is pointwise continuous and strictly increasing on the rational real numbers, it is strictly increasing on the real numbers

```agda
module _
  {l1 l2 : Level}
  (f : pointwise-continuous-function-ℝ l1 l2)
  where

  abstract
    is-strictly-increasing-is-strictly-increasing-rational-ℝ :
      ( (p q : ℚ) → le-ℚ p q →
        le-ℝ
          ( map-pointwise-continuous-function-ℝ f (raise-real-ℚ l1 p))
          ( map-pointwise-continuous-function-ℝ f (raise-real-ℚ l1 q))) →
      is-strictly-increasing-function-ℝ (map-pointwise-continuous-function-ℝ f)
    is-strictly-increasing-is-strictly-increasing-rational-ℝ H =
      is-strictly-increasing-is-strictly-increasing-dense-subset-pointwise-continuous-function-ℝ
        ( f)
        ( dense-subset-rational-real-ℝ l1)
        ( λ (x , p , x~p) (y , q , y~q) x<y →
          binary-tr
            ( le-ℝ)
            ( ap
              ( map-pointwise-continuous-function-ℝ f)
              ( inv ( eq-raise-real-rational-is-rational-ℝ x p x~p)))
            ( ap
              ( map-pointwise-continuous-function-ℝ f)
              ( inv ( eq-raise-real-rational-is-rational-ℝ y q y~q)))
            ( H
              ( p)
              ( q)
              ( reflects-le-real-ℚ
                ( le-le-raise-ℝ l1
                  ( binary-tr
                    ( le-ℝ)
                    ( eq-raise-real-rational-is-rational-ℝ x p x~p)
                    ( eq-raise-real-rational-is-rational-ℝ y q y~q)
                    ( x<y))))))
```
