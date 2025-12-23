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
open import foundation.embeddings
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.strict-order-preserving-maps
open import order-theory.subtypes-strict-preorders

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.classically-pointwise-continuous-functions-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.increasing-functions-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A function `f` from the [real numbers](real-numbers.dedekind-real-numbers.md) to
themselves is
{{#concept "strictly increasing" Disambiguation="function from ℝ to ℝ" Agda=is-strictly-increasing-function-ℝ}}
if for all `x < y`, `f x < f y`.

Several arguments on this page are due to
[Mark Saving](https://math.stackexchange.com/users/798694/mark-saving) in this
Mathematics Stack Exchange answer: <https://math.stackexchange.com/q/5107860>.

## Definition

```agda
is-strictly-increasing-prop-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → Prop (lsuc l1 ⊔ l2)
is-strictly-increasing-prop-function-ℝ {l1} {l2} =
  preserves-strict-order-prop-map-Strict-Preorder
    ( strict-preorder-ℝ l1)
    ( strict-preorder-ℝ l2)

is-strictly-increasing-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-strictly-increasing-function-ℝ f =
  type-Prop (is-strictly-increasing-prop-function-ℝ f)

is-strictly-increasing-on-subset-function-ℝ :
  {l1 l2 l3 : Level} → (ℝ l1 → ℝ l2) → subset-ℝ l3 l1 → UU (lsuc l1 ⊔ l2 ⊔ l3)
is-strictly-increasing-on-subset-function-ℝ {l1} {l2} f S =
  preserves-strict-order-map-Strict-Preorder
    ( strict-preorder-subtype-Strict-Preorder (strict-preorder-ℝ l1) S)
    ( strict-preorder-ℝ l2)
    ( f ∘ inclusion-subset-ℝ S)
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
      is-increasing-is-increasing-on-strict-inequalities-ℝ
        ( f)
        ( λ x y x<y → leq-le-ℝ (H x y x<y))
```

### If a classically pointwise continuous function is strictly increasing on a dense subset of ℝ, then it is strictly increasing on ℝ

```agda
module _
  {l1 l2 l3 : Level}
  (f : classically-pointwise-continuous-map-ℝ l1 l2)
  (S : dense-subset-ℝ l3 l1)
  where

  abstract
    is-strictly-increasing-is-strictly-increasing-dense-subset-classically-pointwise-continuous-map-ℝ :
      is-strictly-increasing-on-subset-function-ℝ
        ( map-classically-pointwise-continuous-map-ℝ f)
        ( subset-dense-subset-ℝ S) →
      is-strictly-increasing-function-ℝ (map-classically-pointwise-continuous-map-ℝ f)
    is-strictly-increasing-is-strictly-increasing-dense-subset-classically-pointwise-continuous-map-ℝ
      H x y x<y =
      let
        H' =
          is-increasing-is-increasing-dense-subset-classically-pointwise-continuous-map-ℝ
            ( f)
            ( S)
            ( is-increasing-is-increasing-on-strict-inequalities-on-subset-function-ℝ
              ( map-classically-pointwise-continuous-map-ℝ f)
              ( subset-dense-subset-ℝ S)
              ( λ a b a<b → leq-le-ℝ (H a b a<b)))
        open
          do-syntax-trunc-Prop
            ( le-prop-ℝ
              ( map-classically-pointwise-continuous-map-ℝ f x)
              ( map-classically-pointwise-continuous-map-ℝ f y))
      in do
        (a , a∈S , x<a , a<y) ← dense-le-dense-subset-ℝ S x<y
        (b , b∈S , a<b , b<y) ← dense-le-dense-subset-ℝ S a<y
        concatenate-leq-le-ℝ
          ( map-classically-pointwise-continuous-map-ℝ f x)
          ( map-classically-pointwise-continuous-map-ℝ f a)
          ( map-classically-pointwise-continuous-map-ℝ f y)
          ( H' x a (leq-le-ℝ x<a))
          ( concatenate-le-leq-ℝ
            ( map-classically-pointwise-continuous-map-ℝ f a)
            ( map-classically-pointwise-continuous-map-ℝ f b)
            ( map-classically-pointwise-continuous-map-ℝ f y)
            ( H (a , a∈S) (b , b∈S) a<b)
            ( H' b y (leq-le-ℝ b<y)))
```

### If `f` is classically pointwise continuous and strictly increasing on the rational real numbers, it is strictly increasing on the real numbers

```agda
module _
  {l1 l2 : Level}
  (f : classically-pointwise-continuous-map-ℝ l1 l2)
  where

  abstract
    is-strictly-increasing-is-strictly-increasing-rational-ℝ :
      ( (p q : ℚ) → le-ℚ p q →
        le-ℝ
          ( map-classically-pointwise-continuous-map-ℝ f (raise-real-ℚ l1 p))
          ( map-classically-pointwise-continuous-map-ℝ f (raise-real-ℚ l1 q))) →
      is-strictly-increasing-function-ℝ (map-classically-pointwise-continuous-map-ℝ f)
    is-strictly-increasing-is-strictly-increasing-rational-ℝ H =
      is-strictly-increasing-is-strictly-increasing-dense-subset-classically-pointwise-continuous-map-ℝ
        ( f)
        ( dense-subset-rational-real-ℝ l1)
        ( λ (x , p , x~p) (y , q , y~q) x<y →
          binary-tr
            ( le-ℝ)
            ( ap
              ( map-classically-pointwise-continuous-map-ℝ f)
              ( inv ( eq-raise-real-rational-is-rational-ℝ x p x~p)))
            ( ap
              ( map-classically-pointwise-continuous-map-ℝ f)
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

### Strictly increasing maps reflect inequality

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  (H : is-strictly-increasing-function-ℝ f)
  where

  abstract
    reflects-leq-is-strictly-increasing-function-ℝ :
      (x y : ℝ l1) →
      leq-ℝ (f x) (f y) →
      leq-ℝ x y
    reflects-leq-is-strictly-increasing-function-ℝ x y fx≤fy =
      leq-not-le-ℝ y x
        ( λ x<y → not-le-leq-ℝ _ _ fx≤fy (H y x x<y))
```

### Classically pointwise continuous, strictly increasing maps reflect strict inequality

```agda
module _
  {l1 l2 : Level}
  (f : classically-pointwise-continuous-map-ℝ l1 l2)
  (H :
    is-strictly-increasing-function-ℝ
      ( map-classically-pointwise-continuous-map-ℝ f))
  where

  abstract
    reflects-le-is-strictly-increasing-classically-pointwise-continuous-map-ℝ :
      (x y : ℝ l1) →
      le-ℝ
        ( map-classically-pointwise-continuous-map-ℝ f x)
        ( map-classically-pointwise-continuous-map-ℝ f y) →
      le-ℝ x y
    reflects-le-is-strictly-increasing-classically-pointwise-continuous-map-ℝ
      x y fx<fy =
      let
        f' = map-classically-pointwise-continuous-map-ℝ f
        open do-syntax-trunc-Prop (le-prop-ℝ x y)
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (ε , fx+ε<y) ← exists-positive-rational-separation-le-ℝ fx<fy
        (δ , Hδ) ←
          is-classically-pointwise-continuous-map-classically-pointwise-continuous-map-ℝ
            ( f)
            ( x)
            ( ε)
        concatenate-le-leq-ℝ
          ( x)
          ( x +ℝ real-ℚ⁺ δ)
          ( y)
          ( le-left-add-real-ℝ⁺ x (positive-real-ℚ⁺ δ))
          ( reflects-leq-is-strictly-increasing-function-ℝ
            ( map-classically-pointwise-continuous-map-ℝ f)
            ( H)
            ( x +ℝ real-ℚ⁺ δ)
            ( y)
            ( chain-of-inequalities
              f' (x +ℝ real-ℚ⁺ δ)
              ≤ f' x +ℝ real-ℚ⁺ ε
                by
                  right-leq-real-bound-neighborhood-ℝ
                    ( ε)
                    ( f' x)
                    ( f' (x +ℝ real-ℚ⁺ δ))
                    ( Hδ (x +ℝ real-ℚ⁺ δ) (neighborhood-right-add-real-ℚ⁺ x δ))
              ≤ f' y by leq-le-ℝ fx+ε<y))
```

### Strictly increasing maps are embeddings

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  (H : is-strictly-increasing-function-ℝ f)
  where

  abstract
    is-injective-is-strictly-increasing-function-ℝ : is-injective f
    is-injective-is-strictly-increasing-function-ℝ {a} {b} fa=fb =
      antisymmetric-leq-ℝ a b
        ( reflects-leq-is-strictly-increasing-function-ℝ
          ( f)
          ( H)
          ( a)
          ( b)
          ( leq-eq-ℝ fa=fb))
        ( reflects-leq-is-strictly-increasing-function-ℝ
          ( f)
          ( H)
          ( b)
          ( a)
          ( leq-eq-ℝ (inv fa=fb)))

    is-emb-is-strictly-increasing-function-ℝ : is-emb f
    is-emb-is-strictly-increasing-function-ℝ =
      is-emb-is-injective
        ( is-set-ℝ l2)
        ( is-injective-is-strictly-increasing-function-ℝ)
```

### The composition of strictly increasing functions is strictly increasing

```agda
module _
  {l1 l2 l3 : Level}
  (f : ℝ l2 → ℝ l3)
  (g : ℝ l1 → ℝ l2)
  where

  abstract
    is-strictly-increasing-comp-is-strictly-increasing-function-ℝ :
      is-strictly-increasing-function-ℝ f →
      is-strictly-increasing-function-ℝ g →
      is-strictly-increasing-function-ℝ (f ∘ g)
    is-strictly-increasing-comp-is-strictly-increasing-function-ℝ H K x y x<y =
      H (g x) (g y) (K x y x<y)
```
