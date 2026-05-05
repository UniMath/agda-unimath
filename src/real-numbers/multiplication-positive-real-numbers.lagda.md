# Multiplication of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.large-posets

open import real-numbers.addition-positive-and-negative-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.cofinal-and-coinitial-endomaps-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-positive-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of pairs of positive real numbers" Agda=mul-ℝ⁺}}
of two [positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) is their
[product](real-numbers.multiplication-real-numbers.md) as real numbers, and is
itself positive.

## Definition

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2}
  where

  abstract opaque
    unfolding mul-ℝ

    is-positive-mul-ℝ :
      is-positive-ℝ x → is-positive-ℝ y → is-positive-ℝ (x *ℝ y)
    is-positive-mul-ℝ 0<x 0<y =
      let open do-syntax-trunc-Prop (is-positive-prop-ℝ (x *ℝ y))
      in do
        (a⁺@(a , _) , a<x) ← exists-ℚ⁺-in-lower-cut-is-positive-ℝ x 0<x
        (b , x<b) ← is-inhabited-upper-cut-ℝ x
        (c⁺@(c , _) , c<y) ← exists-ℚ⁺-in-lower-cut-is-positive-ℝ y 0<y
        (d , y<d) ← is-inhabited-upper-cut-ℝ y
        let
          a<b = le-lower-upper-cut-ℝ x a<x x<b
          b⁺ = (b , is-positive-le-ℚ⁺ a⁺ a<b)
          c<d = le-lower-upper-cut-ℝ y c<y y<d
          d⁺ = (d , is-positive-le-ℚ⁺ c⁺ c<d)
          [a,b] = ((a , b) , leq-le-ℚ a<b)
          [c,d] = ((c , d) , leq-le-ℚ c<d)
        is-positive-exists-ℚ⁺-in-lower-cut-ℝ
          ( x *ℝ y)
          ( intro-exists
            ( min-ℚ⁺
              ( min-ℚ⁺ (a⁺ *ℚ⁺ c⁺) (a⁺ *ℚ⁺ d⁺))
              ( min-ℚ⁺ (b⁺ *ℚ⁺ c⁺) (b⁺ *ℚ⁺ d⁺)))
            ( leq-lower-cut-mul-ℝ'-lower-cut-mul-ℝ x y
              ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
              ( intro-exists
                ( ([a,b] , a<x , x<b) , ([c,d] , c<y , y<d))
                ( refl-leq-ℚ _))))

mul-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → ℝ⁺ (l1 ⊔ l2)
mul-ℝ⁺ (x , is-pos-x) (y , is-pos-y) =
  (x *ℝ y , is-positive-mul-ℝ is-pos-x is-pos-y)

infixl 40 _*ℝ⁺_
_*ℝ⁺_ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → ℝ⁺ (l1 ⊔ l2)
_*ℝ⁺_ = mul-ℝ⁺

ap-mul-ℝ⁺ :
  {l1 l2 : Level} {x x' : ℝ⁺ l1} → x ＝ x' → {y y' : ℝ⁺ l2} → y ＝ y' →
  x *ℝ⁺ y ＝ x' *ℝ⁺ y'
ap-mul-ℝ⁺ = ap-binary mul-ℝ⁺
```

## Properties

### Commutativity of multiplication

```agda
abstract
  commutative-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) → (x *ℝ⁺ y ＝ y *ℝ⁺ x)
  commutative-mul-ℝ⁺ x⁺@(x , _) y⁺@(y , _) =
    eq-ℝ⁺ (x⁺ *ℝ⁺ y⁺) (y⁺ *ℝ⁺ x⁺) (commutative-mul-ℝ x y)
```

### Associativity of multiplication

```agda
abstract
  associative-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) (z : ℝ⁺ l3) →
    ((x *ℝ⁺ y) *ℝ⁺ z) ＝ (x *ℝ⁺ (y *ℝ⁺ z))
  associative-mul-ℝ⁺ (x , _) (y , _) (z , _) =
    eq-ℝ⁺ _ _ (associative-mul-ℝ x y z)
```

### Multiplication by a positive real number preserves and reflects strict inequality

```agda
abstract
  preserves-le-left-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) {y : ℝ l2} {z : ℝ l3} → le-ℝ y z →
    le-ℝ (real-ℝ⁺ x *ℝ y) (real-ℝ⁺ x *ℝ z)
  preserves-le-left-mul-ℝ⁺ x⁺@(x , 0<x) {y} {z} y<z =
    le-is-positive-diff-ℝ
      ( tr
        ( is-positive-ℝ)
        ( left-distributive-mul-diff-ℝ x z y)
        ( is-positive-mul-ℝ 0<x (is-positive-diff-le-ℝ y<z)))

  preserves-le-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) {y : ℝ l2} {z : ℝ l3} → le-ℝ y z →
    le-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x)
  preserves-le-right-mul-ℝ⁺ x y<z =
    binary-tr
      ( le-ℝ)
      ( commutative-mul-ℝ _ _)
      ( commutative-mul-ℝ _ _)
      ( preserves-le-left-mul-ℝ⁺ x y<z)
```

### Multiplication by a positive real number preserves and reflects inequality

```agda
abstract
  preserves-leq-left-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) {y : ℝ l2} {z : ℝ l3} → leq-ℝ y z →
    leq-ℝ (real-ℝ⁺ x *ℝ y) (real-ℝ⁺ x *ℝ z)
  preserves-leq-left-mul-ℝ⁺ x⁺ = preserves-leq-left-mul-ℝ⁰⁺ (nonnegative-ℝ⁺ x⁺)

  preserves-leq-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) {y : ℝ l2} {z : ℝ l3} → leq-ℝ y z →
    leq-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x)
  preserves-leq-right-mul-ℝ⁺ x⁺ =
    preserves-leq-right-mul-ℝ⁰⁺ (nonnegative-ℝ⁺ x⁺)

  reflects-leq-left-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ (real-ℝ⁺ x *ℝ y) (real-ℝ⁺ x *ℝ z) → leq-ℝ y z
  reflects-leq-left-mul-ℝ⁺ x y z xy≤xz =
    leq-not-le-ℝ _ _
      ( λ z<y → not-leq-le-ℝ _ _ (preserves-le-left-mul-ℝ⁺ x z<y) xy≤xz)

  reflects-leq-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x) → leq-ℝ y z
  reflects-leq-right-mul-ℝ⁺ x y z yx≤zx =
    leq-not-le-ℝ _ _
      ( λ z<y → not-leq-le-ℝ _ _ (preserves-le-right-mul-ℝ⁺ x z<y) yx≤zx)
```

### Multiplication preserves similarity

```agda
abstract
  preserves-sim-mul-ℝ⁺ :
    {l1 l2 l3 l4 : Level} →
    (x : ℝ⁺ l1) (x' : ℝ⁺ l2) → sim-ℝ⁺ x x' →
    (y : ℝ⁺ l3) (y' : ℝ⁺ l4) → sim-ℝ⁺ y y' →
    sim-ℝ⁺ (x *ℝ⁺ y) (x' *ℝ⁺ y')
  preserves-sim-mul-ℝ⁺ (x , _) (x' , _) x~x' (y , _) (y' , _) y~y' =
    preserves-sim-mul-ℝ x~x' y~y'

sim-preserving-binary-operator-mul-ℝ⁺ :
  sim-preserving-binary-operator-Cumulative-Large-Set cumulative-large-set-ℝ⁺
sim-preserving-binary-operator-mul-ℝ⁺ =
  make-sim-preserving-binary-operator-Cumulative-Large-Set
    ( cumulative-large-set-ℝ⁺)
    ( mul-ℝ⁺)
    ( λ x x' y y' x~x' y~y' →
      preserves-sim-mul-ℝ⁺ x x' x~x' y y' y~y')
```

### Unit laws

```agda
abstract
  left-unit-law-mul-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → one-ℝ⁺ *ℝ⁺ x ＝ x
  left-unit-law-mul-ℝ⁺ (x , _) = eq-ℝ⁺ _ _ (left-unit-law-mul-ℝ x)

  right-unit-law-mul-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → x *ℝ⁺ one-ℝ⁺ ＝ x
  right-unit-law-mul-ℝ⁺ (x , _) = eq-ℝ⁺ _ _ (right-unit-law-mul-ℝ x)

  left-raise-one-law-mul-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → raise-one-ℝ⁺ l *ℝ⁺ x ＝ x
  left-raise-one-law-mul-ℝ⁺ x = eq-ℝ⁺ _ _ (left-raise-one-law-mul-ℝ _)

  right-raise-one-law-mul-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → x *ℝ⁺ raise-one-ℝ⁺ l ＝ x
  right-raise-one-law-mul-ℝ⁺ x = eq-ℝ⁺ _ _ (right-raise-one-law-mul-ℝ _)
```

### Multiplication by a positive real number is cofinal

```agda
abstract
  is-cofinal-left-mul-real-ℝ⁺ :
    {l1 : Level} (l2 : Level) (x : ℝ⁺ l1) →
    is-cofinal-endomap-ℝ (mul-ℝ {l1} {l2} (real-ℝ⁺ x))
  is-cofinal-left-mul-real-ℝ⁺ l2 x q =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ (ℝ l2) (λ y → leq-prop-ℝ (real-ℚ q) (real-ℝ⁺ x *ℝ y)))
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in do
      (p⁺@(p , _) , p<x) ← exists-ℚ⁺-in-lower-cut-ℝ⁺ x
      (r , q≤pr) ← is-cofinal-left-mul-rational-ℚ⁺ p⁺ q
      let r' = max-ℚ r zero-ℚ
      intro-exists
        ( raise-real-ℚ l2 r')
        ( chain-of-inequalities
          real-ℚ q
          ≤ real-ℚ (p *ℚ r)
            by preserves-leq-real-ℚ q≤pr
          ≤ real-ℚ p *ℝ real-ℚ r
            by leq-eq-ℝ (inv (mul-real-ℚ p r))
          ≤ real-ℚ p *ℝ real-ℚ r'
            by
              preserves-leq-left-mul-ℝ⁺
                ( positive-real-ℚ⁺ p⁺)
                ( preserves-leq-real-ℚ (leq-left-max-ℚ r zero-ℚ))
          ≤ real-ℝ⁺ x *ℝ real-ℚ r'
            by
              preserves-leq-right-mul-ℝ⁰⁺
                ( real-ℚ r' , preserves-leq-real-ℚ (leq-right-max-ℚ r zero-ℚ))
                ( leq-real-is-in-lower-cut-ℝ (real-ℝ⁺ x) p<x)
          ≤ real-ℝ⁺ x *ℝ raise-real-ℚ l2 r'
            by leq-sim-ℝ (preserves-sim-left-mul-ℝ _ _ _ (sim-raise-ℝ l2 _)))

  is-coinitial-left-mul-real-ℝ⁺ :
    {l1 : Level} (l2 : Level) (x : ℝ⁺ l1) →
    is-coinitial-endomap-ℝ (mul-ℝ {l1} {l2} (real-ℝ⁺ x))
  is-coinitial-left-mul-real-ℝ⁺ l2 x q =
    map-exists _
      ( neg-ℝ)
      ( λ y -q≤xy →
        binary-tr
          ( leq-ℝ)
          ( inv (right-negative-law-mul-ℝ _ _))
          ( neg-real-ℚ (neg-ℚ q) ∙ ap real-ℚ (neg-neg-ℚ q))
          ( neg-leq-ℝ -q≤xy))
      ( is-cofinal-left-mul-real-ℝ⁺ l2 x (neg-ℚ q))
```
