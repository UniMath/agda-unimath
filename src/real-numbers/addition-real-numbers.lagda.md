# Addition of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.conjunction
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.transport-along-identifications
open import foundation.existential-quantification
open import elementary-number-theory.rational-numbers
open import real-numbers.dedekind-real-numbers
open import elementary-number-theory.positive-rational-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.addition-lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
open import real-numbers.addition-upper-dedekind-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.negation-real-numbers
open import real-numbers.negation-lower-upper-dedekind-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The sum of two
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) is
is a Dedekind real number whose lower cut (upper cut) is the
the
[Minkowski sum](group-theory.minkowski-multiplication-commutative-monoids.md) of
their lower (upper) cuts.

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  lower-real-add-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-add-ℝ = add-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

  upper-real-add-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-add-ℝ = add-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

  abstract
    is-disjoint-lower-upper-add-ℝ :
      is-disjoint-lower-upper-ℝ lower-real-add-ℝ upper-real-add-ℝ
    is-disjoint-lower-upper-add-ℝ p (p<x+y , x+y<p) =
      do
        ((px , py) , px<x , py<y , p=px+py) ← p<x+y
        ((qx , qy) , x<qx , y<qy , p=qx+qy) ← x+y<p
        irreflexive-le-ℚ
          ( p)
          ( binary-tr
            ( le-ℚ)
            ( inv (p=px+py))
            ( inv (p=qx+qy))
            ( preserves-le-add-ℚ
              { px}
              { qx}
              { py}
              { qy}
              (le-lower-upper-cut-ℝ x px qx px<x x<qx)
              (le-lower-upper-cut-ℝ y py qy py<y y<qy)))
      where open do-syntax-trunc-Prop empty-Prop

    is-arithmetically-located-lower-upper-add-ℝ :
      is-arithmetically-located-lower-upper-ℝ lower-real-add-ℝ upper-real-add-ℝ
    is-arithmetically-located-lower-upper-add-ℝ ε⁺ =
      do
        (px , qx) , qx<px+εx , px<x , x<qx ←
          is-arithmetically-located-lower-upper-real-ℝ x εx⁺
        (py , qy) , qy<py+εy , py<y , y<qy ←
          is-arithmetically-located-lower-upper-real-ℝ y εy⁺
        intro-exists
          ( px +ℚ py , qx +ℚ qy)
          ( tr
              ( le-ℚ (qx +ℚ qy))
              ( equational-reasoning
                  (px +ℚ εx) +ℚ (py +ℚ εy)
                  ＝ (px +ℚ py) +ℚ (εx +ℚ εy)
                    by interchange-law-add-add-ℚ px εx py εy
                  ＝ (px +ℚ py) +ℚ ε
                    by ap ((px +ℚ py) +ℚ_) εx+εy=ε)
              ( preserves-le-add-ℚ
                { qx}
                { px +ℚ εx}
                { qy}
                { py +ℚ εy}
                ( qx<px+εx)
                ( qy<py+εy)) ,
            intro-exists (px , py) (px<x , py<y , refl) ,
            intro-exists (qx , qy) (x<qx , y<qy , refl))
      where
        εx⁺ : ℚ⁺
        εx⁺ = left-summand-split-ℚ⁺ ε⁺
        εy⁺ : ℚ⁺
        εy⁺ = right-summand-split-ℚ⁺ ε⁺
        εx : ℚ
        εx = rational-ℚ⁺ εx⁺
        εy : ℚ
        εy = rational-ℚ⁺ εy⁺
        ε : ℚ
        ε = rational-ℚ⁺ ε⁺
        εx+εy=ε : εx +ℚ εy ＝ ε
        εx+εy=ε = ap rational-ℚ⁺ (eq-add-split-ℚ⁺ ε⁺)
        open
          do-syntax-trunc-Prop
            (∃
              ( ℚ × ℚ)
              ( λ (p , q) →
                le-ℚ-Prop q (p +ℚ ε) ∧
                cut-lower-ℝ lower-real-add-ℝ p ∧
                cut-upper-ℝ upper-real-add-ℝ q))

    is-located-lower-upper-add-ℝ :
      is-located-lower-upper-ℝ lower-real-add-ℝ upper-real-add-ℝ
    is-located-lower-upper-add-ℝ =
      is-located-is-arithmetically-located-lower-upper-ℝ
        ( lower-real-add-ℝ)
        ( upper-real-add-ℝ)
        ( is-arithmetically-located-lower-upper-add-ℝ)

  add-ℝ : ℝ (l1 ⊔ l2)
  pr1 add-ℝ = lower-real-add-ℝ
  pr1 (pr2 add-ℝ) = upper-real-add-ℝ
  pr1 (pr2 (pr2 add-ℝ)) = is-disjoint-lower-upper-add-ℝ
  pr2 (pr2 (pr2 add-ℝ)) = is-located-lower-upper-add-ℝ

infixl 35 _+ℝ_
_+ℝ_ = add-ℝ
```

## Properties

### Addition is commutative

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  commutative-add-ℝ : x +ℝ y ＝ y +ℝ x
  commutative-add-ℝ =
    eq-eq-lower-real-ℝ
      ( x +ℝ y)
      ( y +ℝ x)
      ( commutative-add-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y))
```

### Addition is associative

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  associative-add-ℝ : (x +ℝ y) +ℝ z ＝ x +ℝ (y +ℝ z)
  associative-add-ℝ =
    eq-eq-lower-real-ℝ
      ( (x +ℝ y) +ℝ z)
      ( x +ℝ (y +ℝ z))
      ( associative-add-lower-ℝ
        ( lower-real-ℝ x)
        ( lower-real-ℝ y)
        ( lower-real-ℝ z))
```

### Unit laws for addition

```agda
left-unit-law-add-ℝ : {l : Level} → (x : ℝ l) → zero-ℝ +ℝ x ＝ x
left-unit-law-add-ℝ x =
  eq-eq-lower-real-ℝ
    ( zero-ℝ +ℝ x)
    ( x)
    ( left-unit-law-add-lower-ℝ (lower-real-ℝ x))

right-unit-law-add-ℝ : {l : Level} → (x : ℝ l) → x +ℝ zero-ℝ ＝ x
right-unit-law-add-ℝ x =
  eq-eq-lower-real-ℝ
    ( x +ℝ zero-ℝ)
    ( x)
    ( right-unit-law-add-lower-ℝ (lower-real-ℝ x))
```

### Inverse laws for addition

```agda
left-inverse-law-add-ℝ : {l : Level} → (x : ℝ l) → sim-ℝ (neg-ℝ x +ℝ x) zero-ℝ
pr1 (left-inverse-law-add-ℝ x) r =
  elim-exists
    ( le-ℚ-Prop r zero-ℚ)
    ( λ (p , q) (x<-p , q<x , r=p+q) → {!   !})
```
