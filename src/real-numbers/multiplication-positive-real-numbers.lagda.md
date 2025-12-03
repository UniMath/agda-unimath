# Multiplication of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.large-posets

open import real-numbers.addition-positive-and-negative-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
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

  reflects-le-left-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) {y : ℝ l2} {z : ℝ l3} →
    le-ℝ (real-ℝ⁺ x *ℝ y) (real-ℝ⁺ x *ℝ z) → le-ℝ y z
  reflects-le-left-mul-ℝ⁺ x {y} {z} xy<xz =
    preserves-le-sim-ℝ
      ( cancel-left-div-mul-ℝ⁺ x y)
      ( cancel-left-div-mul-ℝ⁺ x z)
      ( preserves-le-left-mul-ℝ⁺ (inv-ℝ⁺ x) xy<xz)

  preserves-le-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) {y : ℝ l2} {z : ℝ l3} → le-ℝ y z →
    le-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x)
  preserves-le-right-mul-ℝ⁺ x y<z =
    binary-tr
      ( le-ℝ)
      ( commutative-mul-ℝ _ _)
      ( commutative-mul-ℝ _ _)
      ( preserves-le-left-mul-ℝ⁺ x y<z)

  reflects-le-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) {y : ℝ l2} {z : ℝ l3} →
    le-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x) → le-ℝ y z
  reflects-le-right-mul-ℝ⁺ x yx<zx =
    reflects-le-left-mul-ℝ⁺ x
      ( binary-tr
        ( le-ℝ)
        ( commutative-mul-ℝ _ _)
        ( commutative-mul-ℝ _ _)
        ( yx<zx))
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
    preserves-leq-sim-ℝ
      ( cancel-left-div-mul-ℝ⁺ x y)
      ( cancel-left-div-mul-ℝ⁺ x z)
      ( preserves-leq-left-mul-ℝ⁺ (inv-ℝ⁺ x) xy≤xz)

  reflects-leq-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x) → leq-ℝ y z
  reflects-leq-right-mul-ℝ⁺ x y z yx≤zx =
    reflects-leq-left-mul-ℝ⁺ x y z
      ( binary-tr
        ( leq-ℝ)
        ( commutative-mul-ℝ _ _)
        ( commutative-mul-ℝ _ _)
        ( yx≤zx))
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
```

### Unit laws

```agda
abstract
  left-unit-law-mul-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → one-ℝ⁺ *ℝ⁺ x ＝ x
  left-unit-law-mul-ℝ⁺ (x , _) = eq-ℝ⁺ _ _ (left-unit-law-mul-ℝ x)

  right-unit-law-mul-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → x *ℝ⁺ one-ℝ⁺ ＝ x
  right-unit-law-mul-ℝ⁺ (x , _) = eq-ℝ⁺ _ _ (right-unit-law-mul-ℝ x)
```

### Inverse laws

```agda
module _
  {l : Level} (x : ℝ⁺ l)
  where

  abstract
    eq-right-inverse-law-mul-ℝ⁺ :
      x *ℝ⁺ inv-ℝ⁺ x ＝ raise-ℝ⁺ l one-ℝ⁺
    eq-right-inverse-law-mul-ℝ⁺ =
      eq-sim-ℝ⁺ _ _
        ( transitive-sim-ℝ _ _ _
          ( sim-raise-ℝ l one-ℝ)
          ( right-inverse-law-mul-ℝ⁺ x))

    eq-left-inverse-law-mul-ℝ⁺ :
      inv-ℝ⁺ x *ℝ⁺ x ＝ raise-ℝ⁺ l one-ℝ⁺
    eq-left-inverse-law-mul-ℝ⁺ =
      eq-sim-ℝ⁺ _ _
        ( transitive-sim-ℝ _ _ _
          ( sim-raise-ℝ l one-ℝ)
          ( left-inverse-law-mul-ℝ⁺ x))
```

### The multiplicative inverse is distributive over multiplication

```agda
abstract
  distributive-real-inv-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    real-inv-ℝ⁺ (x *ℝ⁺ y) ＝ real-inv-ℝ⁺ x *ℝ real-inv-ℝ⁺ y
  distributive-real-inv-mul-ℝ⁺ x⁺@(x , _) y⁺@(y , _) =
    eq-sim-ℝ
      ( symmetric-sim-ℝ
        ( unique-right-inv-ℝ⁺
          ( x⁺ *ℝ⁺ y⁺)
          ( inv-ℝ⁺ x⁺ *ℝ⁺ inv-ℝ⁺ y⁺)
          ( similarity-reasoning-ℝ
            (x *ℝ y) *ℝ (real-inv-ℝ⁺ x⁺ *ℝ real-inv-ℝ⁺ y⁺)
            ~ℝ (x *ℝ real-inv-ℝ⁺ x⁺) *ℝ (y *ℝ real-inv-ℝ⁺ y⁺)
              by sim-eq-ℝ (interchange-law-mul-mul-ℝ _ _ _ _)
            ~ℝ one-ℝ *ℝ one-ℝ
              by
                preserves-sim-mul-ℝ
                  ( right-inverse-law-mul-ℝ⁺ x⁺)
                  ( right-inverse-law-mul-ℝ⁺ y⁺)
            ~ℝ one-ℝ
              by sim-eq-ℝ (left-unit-law-mul-ℝ one-ℝ))))
```

### For nonnegative `x`, `(x + ε)⁻¹ x ≤ 1`

```agda
abstract
  leq-one-mul-inv-add-positive-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁺ l2) →
    leq-ℝ (real-inv-ℝ⁺ (add-nonnegative-positive-ℝ x y) *ℝ real-ℝ⁰⁺ x) one-ℝ
  leq-one-mul-inv-add-positive-ℝ⁰⁺ x⁰⁺@(x , _) y⁺@(y , _) =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      chain-of-inequalities
      real-inv-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺) *ℝ x
      ≤ real-inv-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺) *ℝ (x +ℝ y)
        by
          preserves-leq-left-mul-ℝ⁺
            ( inv-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺))
            ( leq-left-add-real-ℝ⁺ x y⁺)
      ≤ one-ℝ
        by
          leq-sim-ℝ
            ( left-inverse-law-mul-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺))
```
