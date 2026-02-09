# Strict inequality of MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequality-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-disjunction
open import foundation.functoriality-propositional-truncation
open import foundation.large-binary-relations
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universe-levels

open import logic.double-negation-elimination
open import logic.functoriality-existential-quantification
open import logic.irrefutable-types

open import order-theory.similarity-of-elements-strict-preorders
open import order-theory.strict-orders
open import order-theory.strict-preorders

open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-macneille-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="MacNeille real numbers" Agda=le-macneille-ℝ}}
on the [MacNeille real numbers](real-numbers.macneille-real-numbers.md) is
defined as the presence of a
[rational number](elementary-number-theory.rational-numbers.md) between them.

```agda
opaque
  le-macneille-ℝ : Large-Relation _⊔_ macneille-ℝ
  le-macneille-ℝ x y =
    exists ℚ (λ q → upper-cut-macneille-ℝ x q ∧ lower-cut-macneille-ℝ y q)

  is-prop-le-macneille-ℝ :
    {l1 l2 : Level}
    (x : macneille-ℝ l1) (y : macneille-ℝ l2) →
    is-prop (le-macneille-ℝ x y)
  is-prop-le-macneille-ℝ x y =
    is-prop-exists ℚ
      ( λ q → upper-cut-macneille-ℝ x q ∧ lower-cut-macneille-ℝ y q)

le-prop-macneille-ℝ : Large-Relation-Prop _⊔_ macneille-ℝ
le-prop-macneille-ℝ x y = (le-macneille-ℝ x y , is-prop-le-macneille-ℝ x y)
```

## Properties

### Lower and upper cuts are closed under the standard ordering on the rationals

```agda
module _
  {l : Level} (x : macneille-ℝ l) {p q : ℚ}
  where

  le-lower-cut-macneille-ℝ :
    le-ℚ p q →
    is-in-lower-cut-macneille-ℝ x q →
    is-in-lower-cut-macneille-ℝ x p
  le-lower-cut-macneille-ℝ =
    is-in-cut-le-ℚ-lower-ℝ (lower-real-macneille-ℝ x) p q

  leq-lower-cut-macneille-ℝ :
    leq-ℚ p q →
    is-in-lower-cut-macneille-ℝ x q →
    is-in-lower-cut-macneille-ℝ x p
  leq-lower-cut-macneille-ℝ =
    is-in-cut-leq-ℚ-lower-ℝ (lower-real-macneille-ℝ x) p q

  le-upper-cut-macneille-ℝ :
    le-ℚ p q →
    is-in-upper-cut-macneille-ℝ x p →
    is-in-upper-cut-macneille-ℝ x q
  le-upper-cut-macneille-ℝ =
    is-in-cut-le-ℚ-upper-ℝ (upper-real-macneille-ℝ x) p q

  leq-upper-cut-macneille-ℝ :
    leq-ℚ p q →
    is-in-upper-cut-macneille-ℝ x p →
    is-in-upper-cut-macneille-ℝ x q
  leq-upper-cut-macneille-ℝ =
    is-in-cut-leq-ℚ-upper-ℝ (upper-real-macneille-ℝ x) p q
```

### The MacNeille cuts are rounded

```agda
module _
  {l : Level} (x : macneille-ℝ l)
  where

  is-rounded-lower-cut-macneille-ℝ :
    (q : ℚ) →
    is-in-lower-cut-macneille-ℝ x q ↔
    exists ℚ (λ r → (le-ℚ-Prop q r) ∧ (lower-cut-macneille-ℝ x r))
  is-rounded-lower-cut-macneille-ℝ =
    is-rounded-cut-lower-ℝ (lower-real-macneille-ℝ x)

  is-rounded-upper-cut-macneille-ℝ :
    (r : ℚ) →
    is-in-upper-cut-macneille-ℝ x r ↔
    exists ℚ (λ q → (le-ℚ-Prop q r) ∧ (upper-cut-macneille-ℝ x q))
  is-rounded-upper-cut-macneille-ℝ =
    is-rounded-cut-upper-ℝ (upper-real-macneille-ℝ x)
```

### Elements of the lower cut are lower bounds of the upper cut

```agda
module _
  {l : Level} (x : macneille-ℝ l) {p q : ℚ}
  where

  abstract
    le-lower-upper-cut-macneille-ℝ :
      is-in-lower-cut-macneille-ℝ x p →
      is-in-upper-cut-macneille-ℝ x q →
      le-ℚ p q
    le-lower-upper-cut-macneille-ℝ H H' =
      rec-coproduct
        ( id)
        ( λ I →
          ex-falso
            ( is-disjoint-cut-macneille-ℝ x p
              ( H , leq-upper-cut-macneille-ℝ x I H')))
        ( decide-le-leq-ℚ p q)

    leq-lower-upper-cut-macneille-ℝ :
      is-in-lower-cut-macneille-ℝ x p →
      is-in-upper-cut-macneille-ℝ x q →
      leq-ℚ p q
    leq-lower-upper-cut-macneille-ℝ H H' =
      leq-le-ℚ (le-lower-upper-cut-macneille-ℝ H H')
```

### Strict inequality on the MacNeille reals implies inequality

```agda
abstract opaque
  unfolding le-macneille-ℝ

  leq-le-macneille-ℝ :
    {l1 l2 : Level} {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    le-macneille-ℝ x y → leq-macneille-ℝ x y
  leq-le-macneille-ℝ {x = x} {y = y} x<y =
    leq-macneille-leq-lower-real-macneille-ℝ x y
      ( λ p p<x →
        elim-exists
          ( lower-cut-macneille-ℝ y p)
          ( λ q (x<q , q<y) →
            le-lower-cut-macneille-ℝ y
              ( le-lower-upper-cut-macneille-ℝ x p<x x<q)
              ( q<y))
          ( x<y))
```

### Strict inequality on the MacNeille reals is irreflexive

```agda
abstract opaque
  unfolding le-macneille-ℝ

  irreflexive-le-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) → ¬ (le-macneille-ℝ x x)
  irreflexive-le-macneille-ℝ x =
    elim-exists
      ( empty-Prop)
      ( λ q (x<q , q<x) → is-disjoint-cut-macneille-ℝ x q (q<x , x<q))
```

### Strict inequality on the MacNeille reals is asymmetric

```agda
module _
  {l1 l2 : Level} {x : macneille-ℝ l1} {y : macneille-ℝ l2}
  where

  abstract opaque
    unfolding le-macneille-ℝ

    asymmetric-le-macneille-ℝ :
      le-macneille-ℝ x y → ¬ (le-macneille-ℝ y x)
    asymmetric-le-macneille-ℝ x<y y<x =
      let
        open do-syntax-trunc-Prop empty-Prop
      in do
        ( p , x<p , p<y) ← x<y
        ( q , y<q , q<x) ← y<x
        rec-coproduct
          ( asymmetric-le-ℚ
            ( q)
            ( p)
            ( le-lower-upper-cut-macneille-ℝ x q<x x<p))
          ( not-leq-le-ℚ
            ( p)
            ( q)
            ( le-lower-upper-cut-macneille-ℝ y p<y y<q))
          ( decide-le-leq-ℚ p q)
```

### Strict inequality on the MacNeille reals is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : macneille-ℝ l1)
  (y : macneille-ℝ l2)
  (z : macneille-ℝ l3)
  where

  abstract opaque
    unfolding le-macneille-ℝ

    transitive-le-macneille-ℝ :
      le-macneille-ℝ y z → le-macneille-ℝ x y → le-macneille-ℝ x z
    transitive-le-macneille-ℝ y<z x<y =
      let
        open do-syntax-trunc-Prop (le-prop-macneille-ℝ x z)
      in do
        ( p , x<p , p<y) ← x<y
        ( q , y<q , q<z) ← y<z
        intro-exists
          ( p)
          ( x<p ,
            le-lower-cut-macneille-ℝ z
              ( le-lower-upper-cut-macneille-ℝ y p<y y<q)
              ( q<z))
```

### Strict inequality on the MacNeille reals is invariant under similarity

```agda
module _
  {l1 l2 l3 : Level}
  (z : macneille-ℝ l1) (x : macneille-ℝ l2) (y : macneille-ℝ l3)
  (x~y : sim-macneille-ℝ x y)
  where

  abstract opaque
    unfolding le-macneille-ℝ sim-macneille-ℝ

    preserves-le-left-sim-macneille-ℝ :
      le-macneille-ℝ x z → le-macneille-ℝ y z
    preserves-le-left-sim-macneille-ℝ =
      map-tot-exists
        ( λ q →
          map-product
            ( pr1 (sim-upper-cut-sim-macneille-ℝ x y x~y) q)
            ( id))

    preserves-le-right-sim-macneille-ℝ :
      le-macneille-ℝ z x → le-macneille-ℝ z y
    preserves-le-right-sim-macneille-ℝ =
      map-tot-exists ( λ q → map-product id (pr1 x~y q))

module _
  {l1 l2 l3 l4 : Level}
  {x1 : macneille-ℝ l1} {x2 : macneille-ℝ l2}
  {y1 : macneille-ℝ l3} {y2 : macneille-ℝ l4}
  (x1~x2 : sim-macneille-ℝ x1 x2)
  (y1~y2 : sim-macneille-ℝ y1 y2)
  where

  preserves-le-sim-macneille-ℝ :
    le-macneille-ℝ x1 y1 → le-macneille-ℝ x2 y2
  preserves-le-sim-macneille-ℝ x1<y1 =
    preserves-le-left-sim-macneille-ℝ
      ( y2)
      ( x1)
      ( x2)
      ( x1~x2)
      ( preserves-le-right-sim-macneille-ℝ x1 y1 y2 y1~y2 x1<y1)
```

### Similarity implies inequality

```agda
module _
  {l1 l2 : Level} {x : macneille-ℝ l1} {y : macneille-ℝ l2}
  where

  abstract opaque
    unfolding sim-macneille-ℝ

    leq-sim-macneille-ℝ : sim-macneille-ℝ x y → leq-macneille-ℝ x y
    leq-sim-macneille-ℝ x~y =
      leq-macneille-leq-lower-real-macneille-ℝ x y (pr1 x~y)

    leq-sim-macneille-ℝ' : sim-macneille-ℝ x y → leq-macneille-ℝ y x
    leq-sim-macneille-ℝ' x~y =
      leq-macneille-leq-lower-real-macneille-ℝ y x (pr2 x~y)

    sim-sim-leq-macneille-ℝ :
      leq-macneille-ℝ x y × leq-macneille-ℝ y x → sim-macneille-ℝ x y
    sim-sim-leq-macneille-ℝ (x≤y , y≤x) = (pr1 x≤y , pr1 y≤x)

    sim-leq-sim-macneille-ℝ :
      sim-macneille-ℝ x y → leq-macneille-ℝ x y × leq-macneille-ℝ y x
    sim-leq-sim-macneille-ℝ x~y =
      ( leq-sim-macneille-ℝ x~y , leq-sim-macneille-ℝ' x~y)
```

### Raising the universe level of either side of a strict inequality

```agda
abstract
  preserves-le-left-raise-macneille-ℝ :
    {l1 l2 : Level} (l : Level)
    {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    le-macneille-ℝ x y → le-macneille-ℝ (raise-macneille-ℝ l x) y
  preserves-le-left-raise-macneille-ℝ l {x} {y} =
    preserves-le-left-sim-macneille-ℝ _ _ _
      ( sim-raise-macneille-ℝ l x)

  reflects-le-left-raise-macneille-ℝ :
    {l1 l2 : Level} (l : Level)
    {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    le-macneille-ℝ (raise-macneille-ℝ l x) y → le-macneille-ℝ x y
  reflects-le-left-raise-macneille-ℝ l {x} {y} =
    preserves-le-left-sim-macneille-ℝ _ _ _
      ( sim-raise-macneille-ℝ' l x)

  preserves-le-right-raise-macneille-ℝ :
    {l1 l2 : Level} (l : Level)
    {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    le-macneille-ℝ x y → le-macneille-ℝ x (raise-macneille-ℝ l y)
  preserves-le-right-raise-macneille-ℝ l {x} {y} =
    preserves-le-right-sim-macneille-ℝ _ _ _
      ( sim-raise-macneille-ℝ l y)

  reflects-le-right-raise-macneille-ℝ :
    {l1 l2 : Level} (l : Level)
    {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    le-macneille-ℝ x (raise-macneille-ℝ l y) → le-macneille-ℝ x y
  reflects-le-right-raise-macneille-ℝ l {x} {y} =
    preserves-le-right-sim-macneille-ℝ _ _ _
      ( sim-raise-macneille-ℝ' l y)

  le-iff-le-right-raise-macneille-ℝ :
    {l1 l2 : Level} (l : Level)
    (x : macneille-ℝ l1) (y : macneille-ℝ l2) →
    le-macneille-ℝ x y ↔ le-macneille-ℝ x (raise-macneille-ℝ l y)
  le-iff-le-right-raise-macneille-ℝ l x y =
    ( preserves-le-right-raise-macneille-ℝ l ,
      reflects-le-right-raise-macneille-ℝ l)
```

### The inclusion of the rationals preserves and reflects strict inequality

```agda
module _
  {x y : ℚ}
  where

  abstract opaque
    unfolding le-macneille-ℝ real-ℚ

    preserves-le-macneille-real-ℚ :
      le-ℚ x y → le-macneille-ℝ (macneille-real-ℚ x) (macneille-real-ℚ y)
    preserves-le-macneille-real-ℚ = dense-le-ℚ

    reflects-le-macneille-real-ℚ :
      le-macneille-ℝ (macneille-real-ℚ x) (macneille-real-ℚ y) → le-ℚ x y
    reflects-le-macneille-real-ℚ =
      elim-exists
        ( le-ℚ-Prop x y)
        ( λ q (x<q , q<y) → transitive-le-ℚ x q y q<y x<q)

  iff-le-macneille-real-ℚ :
    le-ℚ x y ↔ le-macneille-ℝ (macneille-real-ℚ x) (macneille-real-ℚ y)
  pr1 iff-le-macneille-real-ℚ = preserves-le-macneille-real-ℚ
  pr2 iff-le-macneille-real-ℚ = reflects-le-macneille-real-ℚ
```

### Concatenation rules for inequality and strict inequality

```agda
module _
  {l1 l2 l3 : Level}
  (x : macneille-ℝ l1)
  (y : macneille-ℝ l2)
  (z : macneille-ℝ l3)
  where

  abstract opaque
    unfolding le-macneille-ℝ

    concatenate-le-leq-macneille-ℝ :
      le-macneille-ℝ x y → leq-macneille-ℝ y z → le-macneille-ℝ x z
    concatenate-le-leq-macneille-ℝ x<y y≤z =
      map-tot-exists (λ p → map-product id (pr1 y≤z p)) x<y

    concatenate-leq-le-macneille-ℝ :
      leq-macneille-ℝ x y → le-macneille-ℝ y z → le-macneille-ℝ x z
    concatenate-leq-le-macneille-ℝ x≤y =
      map-tot-exists
        ( λ p → map-product (pr2 x≤y p) id)
```

### A rational is in the lower cut of `x` iff its MacNeille real projection is less than `x`

```agda
module _
  {l : Level} {q : ℚ} (x : macneille-ℝ l)
  where

  abstract opaque
    unfolding le-macneille-ℝ real-ℚ

    le-real-iff-is-in-lower-cut-macneille-ℝ :
      is-in-lower-cut-macneille-ℝ x q ↔ le-macneille-ℝ (macneille-real-ℚ q) x
    le-real-iff-is-in-lower-cut-macneille-ℝ =
      is-rounded-lower-cut-macneille-ℝ x q

  abstract
    le-real-is-in-lower-cut-macneille-ℝ :
      is-in-lower-cut-macneille-ℝ x q → le-macneille-ℝ (macneille-real-ℚ q) x
    le-real-is-in-lower-cut-macneille-ℝ =
      forward-implication le-real-iff-is-in-lower-cut-macneille-ℝ

    is-in-lower-cut-le-macneille-real-ℚ :
      le-macneille-ℝ (macneille-real-ℚ q) x → is-in-lower-cut-macneille-ℝ x q
    is-in-lower-cut-le-macneille-real-ℚ =
      backward-implication le-real-iff-is-in-lower-cut-macneille-ℝ

    leq-real-is-in-lower-cut-macneille-ℝ :
      is-in-lower-cut-macneille-ℝ x q → leq-macneille-ℝ (macneille-real-ℚ q) x
    leq-real-is-in-lower-cut-macneille-ℝ q<x =
      leq-le-macneille-ℝ (le-real-is-in-lower-cut-macneille-ℝ q<x)

module _
  {l : Level} (l1 : Level) {q : ℚ} (x : macneille-ℝ l)
  where

  abstract
    le-raise-real-is-in-lower-cut-macneille-ℝ :
      is-in-lower-cut-macneille-ℝ x q →
      le-macneille-ℝ (raise-macneille-ℝ l1 (macneille-real-ℚ q)) x
    le-raise-real-is-in-lower-cut-macneille-ℝ q<x =
      preserves-le-left-sim-macneille-ℝ _ _ _
        ( sim-raise-macneille-ℝ l1 (macneille-real-ℚ q))
        ( le-real-is-in-lower-cut-macneille-ℝ x q<x)

    is-in-lower-cut-le-raise-macneille-real-ℚ :
      le-macneille-ℝ (raise-macneille-ℝ l1 (macneille-real-ℚ q)) x →
      is-in-lower-cut-macneille-ℝ x q
    is-in-lower-cut-le-raise-macneille-real-ℚ l1q<x =
      is-in-lower-cut-le-macneille-real-ℚ
        ( x)
        ( preserves-le-left-sim-macneille-ℝ _ _ _
          ( sim-raise-macneille-ℝ' l1 _)
          ( l1q<x))
```

### A rational is in the upper cut of `x` iff its MacNeille real projection is greater than `x`

```agda
module _
  {l : Level} {q : ℚ} (x : macneille-ℝ l)
  where

  abstract opaque
    unfolding le-macneille-ℝ real-ℚ

    le-real-iff-is-in-upper-cut-macneille-ℝ :
      is-in-upper-cut-macneille-ℝ x q ↔ le-macneille-ℝ x (macneille-real-ℚ q)
    le-real-iff-is-in-upper-cut-macneille-ℝ =
      iff-tot-exists (λ _ → iff-equiv commutative-product) ∘iff
      is-rounded-upper-cut-macneille-ℝ x q

  abstract
    le-real-is-in-upper-cut-macneille-ℝ :
      is-in-upper-cut-macneille-ℝ x q → le-macneille-ℝ x (macneille-real-ℚ q)
    le-real-is-in-upper-cut-macneille-ℝ =
      forward-implication le-real-iff-is-in-upper-cut-macneille-ℝ

    is-in-upper-cut-le-macneille-real-ℚ :
      le-macneille-ℝ x (macneille-real-ℚ q) → is-in-upper-cut-macneille-ℝ x q
    is-in-upper-cut-le-macneille-real-ℚ =
      backward-implication le-real-iff-is-in-upper-cut-macneille-ℝ

    leq-real-is-in-upper-cut-macneille-ℝ :
      is-in-upper-cut-macneille-ℝ x q → leq-macneille-ℝ x (macneille-real-ℚ q)
    leq-real-is-in-upper-cut-macneille-ℝ x<q =
      leq-le-macneille-ℝ (le-real-is-in-upper-cut-macneille-ℝ x<q)

module _
  {l : Level} (l1 : Level) {q : ℚ} (x : macneille-ℝ l)
  where

  abstract
    le-raise-real-is-in-upper-cut-macneille-ℝ :
      is-in-upper-cut-macneille-ℝ x q →
      le-macneille-ℝ x (raise-macneille-ℝ l1 (macneille-real-ℚ q))
    le-raise-real-is-in-upper-cut-macneille-ℝ x<q =
      preserves-le-right-sim-macneille-ℝ _ _ _
        ( sim-raise-macneille-ℝ l1 (macneille-real-ℚ q))
        ( le-real-is-in-upper-cut-macneille-ℝ x x<q)
```

### Every MacNeille real is less than a rational number

```agda
module _
  {l : Level} (x : macneille-ℝ l)
  where

  abstract
    exists-greater-rational-macneille-ℝ :
      exists ℚ (λ q → le-prop-macneille-ℝ x (macneille-real-ℚ q))
    exists-greater-rational-macneille-ℝ =
      map-tot-exists
        ( λ q → le-real-is-in-upper-cut-macneille-ℝ x)
        ( is-inhabited-upper-cut-macneille-ℝ x)

    exists-lesser-rational-macneille-ℝ :
      exists ℚ (λ q → le-prop-macneille-ℝ (macneille-real-ℚ q) x)
    exists-lesser-rational-macneille-ℝ =
      map-tot-exists
        ( λ q → le-real-is-in-lower-cut-macneille-ℝ x)
        ( is-inhabited-lower-cut-macneille-ℝ x)
```

### The MacNeille reals have no lower or upper bound

```agda
module _
  {l : Level}
  (x : macneille-ℝ l)
  where

  abstract
    exists-lesser-macneille-ℝ :
      exists (macneille-ℝ lzero) (λ y → le-prop-macneille-ℝ y x)
    exists-lesser-macneille-ℝ =
      map-exists
        ( λ y → le-macneille-ℝ y x)
        ( macneille-real-ℚ)
        ( λ q → le-real-is-in-lower-cut-macneille-ℝ x)
        ( is-inhabited-lower-cut-macneille-ℝ x)

    exists-greater-macneille-ℝ :
      exists (macneille-ℝ lzero) (λ y → le-prop-macneille-ℝ x y)
    exists-greater-macneille-ℝ =
      map-exists
        ( le-macneille-ℝ x)
        ( macneille-real-ℚ)
        ( λ q → le-real-is-in-upper-cut-macneille-ℝ x)
        ( is-inhabited-upper-cut-macneille-ℝ x)
```

### If `x` is less than `y`, then `y` is not less than or equal to `x`

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  abstract opaque
    unfolding le-macneille-ℝ

    not-leq-le-macneille-ℝ : le-macneille-ℝ x y → ¬ (leq-macneille-ℝ y x)
    not-leq-le-macneille-ℝ x<y y≤x =
      elim-exists
        ( empty-Prop)
        ( λ q (x<q , q<y) →
          is-disjoint-cut-macneille-ℝ x q (pr1 y≤x q q<y , x<q))
        ( x<y)
```

### If `x` is less than `y`, then `x` is not similar to `y`

```agda
abstract
  not-sim-le-macneille-ℝ :
    {l1 l2 : Level}
    {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    le-macneille-ℝ x y → ¬ sim-macneille-ℝ x y
  not-sim-le-macneille-ℝ {x = x} {y = y} x<y x~y =
    not-leq-le-macneille-ℝ x y x<y
      ( leq-sim-macneille-ℝ (symmetric-sim-macneille-ℝ x~y))
```

### If `x` is less than or equal to `y`, then `y` is not less than `x`

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  not-le-leq-macneille-ℝ : leq-macneille-ℝ x y → ¬ (le-macneille-ℝ y x)
  not-le-leq-macneille-ℝ x≤y y<x = not-leq-le-macneille-ℝ y x y<x x≤y
```

### The rational numbers are dense in the MacNeille real numbers

```agda
module _
  {l1 l2 : Level}
  (x : macneille-ℝ l1)
  (y : macneille-ℝ l2)
  where

  abstract opaque
    unfolding le-macneille-ℝ

    dense-rational-le-macneille-ℝ :
      le-macneille-ℝ x y →
      exists ℚ
        ( λ z →
          le-prop-macneille-ℝ x (macneille-real-ℚ z) ∧
          le-prop-macneille-ℝ (macneille-real-ℚ z) y)
    dense-rational-le-macneille-ℝ =
      map-tot-exists
        ( λ q →
          map-product
            ( le-real-is-in-upper-cut-macneille-ℝ x)
            ( le-real-is-in-lower-cut-macneille-ℝ y))
```

### Strict inequality on the MacNeille real numbers is dense

```agda
module _
  {l1 l2 : Level}
  (x : macneille-ℝ l1)
  (y : macneille-ℝ l2)
  where

  abstract
    dense-le-macneille-ℝ :
      le-macneille-ℝ x y →
      exists
        ( macneille-ℝ lzero)
        ( λ z → le-prop-macneille-ℝ x z ∧ le-prop-macneille-ℝ z y)
    dense-le-macneille-ℝ x<y =
      map-exists-map-base
        ( _)
        ( macneille-real-ℚ)
        ( dense-rational-le-macneille-ℝ x y x<y)
```

### `x < y` iff `raise-macneille-ℝ l x < raise-macneille-ℝ l y`

```agda
abstract
  le-le-raise-macneille-ℝ :
    {l1 l2 : Level} (l : Level) {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    le-macneille-ℝ (raise-macneille-ℝ l x) (raise-macneille-ℝ l y) →
    le-macneille-ℝ x y
  le-le-raise-macneille-ℝ l {x} {y} =
    preserves-le-sim-macneille-ℝ
      ( sim-raise-macneille-ℝ' l x)
      ( sim-raise-macneille-ℝ' l y)

  le-raise-le-macneille-ℝ :
    {l1 l2 : Level} (l : Level)
    {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    le-macneille-ℝ x y →
    le-macneille-ℝ (raise-macneille-ℝ l x) (raise-macneille-ℝ l y)
  le-raise-le-macneille-ℝ l {x} {y} =
    preserves-le-sim-macneille-ℝ
      ( sim-raise-macneille-ℝ l x)
      ( sim-raise-macneille-ℝ l y)
```

### If `x` is less than each rational number `y` is less than, then `x ≤ y`

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  abstract opaque
    leq-le-rational-macneille-ℝ :
      ( (q : ℚ) →
        le-macneille-ℝ y (macneille-real-ℚ q) →
        le-macneille-ℝ x (macneille-real-ℚ q)) →
      leq-macneille-ℝ x y
    leq-le-rational-macneille-ℝ H =
      leq-macneille-leq-upper-real-macneille-ℝ x y
        ( λ q y<q →
          is-in-upper-cut-le-macneille-real-ℚ x
            ( H q (le-real-is-in-upper-cut-macneille-ℝ y y<q)))
```

### Two MacNeille real numbers are similar if they are less than the same rational numbers

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  abstract
    sim-le-same-rational-macneille-ℝ :
      ( (q : ℚ) →
        le-macneille-ℝ x (macneille-real-ℚ q) ↔
        le-macneille-ℝ y (macneille-real-ℚ q)) →
      sim-macneille-ℝ x y
    sim-le-same-rational-macneille-ℝ H =
      sim-sim-leq-macneille-ℝ
        ( leq-le-rational-macneille-ℝ x y (backward-implication ∘ H) ,
          leq-le-rational-macneille-ℝ y x (forward-implication ∘ H))
```

### `0 < 1`

```agda
le-zero-one-macneille-ℝ :
  le-macneille-ℝ zero-macneille-ℝ one-macneille-ℝ
le-zero-one-macneille-ℝ =
  preserves-le-macneille-real-ℚ le-zero-one-ℚ
```

### For any MacNeille real number, there exists a greater positive rational number

```agda
abstract
  exists-greater-positive-rational-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) →
    exists ℚ⁺ (λ q → le-prop-macneille-ℝ x (macneille-real-ℚ⁺ q))
  exists-greater-positive-rational-macneille-ℝ x =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ℚ⁺ (λ q → le-prop-macneille-ℝ x (macneille-real-ℚ⁺ q)))
    in do
      (p , x<p) ← is-inhabited-upper-cut-macneille-ℝ x
      let q = max-ℚ p one-ℚ
      intro-exists
        ( q ,
          is-positive-le-zero-ℚ
            ( concatenate-le-leq-ℚ
              ( zero-ℚ)
              ( one-ℚ)
              ( q)
              ( le-zero-one-ℚ)
              ( leq-right-max-ℚ p one-ℚ)))
        ( le-real-is-in-upper-cut-macneille-ℝ
          ( x)
          ( leq-upper-cut-macneille-ℝ x (leq-left-max-ℚ p one-ℚ) x<p))
```

### If `q ≤ x ⇒ q ≤ y` for every rational `q`, then `x ≤ y`

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  abstract
    leq-leq-rational-macneille-ℝ' :
      ( (q : ℚ) →
        leq-macneille-ℝ (macneille-real-ℚ q) x →
        leq-macneille-ℝ (macneille-real-ℚ q) y) →
      leq-macneille-ℝ x y
    leq-leq-rational-macneille-ℝ' H =
      leq-macneille-leq-lower-real-macneille-ℝ x y
        ( λ q q<x →
          let
            open do-syntax-trunc-Prop (lower-cut-macneille-ℝ y q)
          in do
            (r , q<r , r<x) ←
              forward-implication (is-rounded-lower-cut-macneille-ℝ x q) q<x
            is-in-lower-cut-le-macneille-real-ℚ
              ( y)
              ( concatenate-le-leq-macneille-ℝ
                ( macneille-real-ℚ q)
                ( macneille-real-ℚ r)
                ( y)
                ( preserves-le-macneille-real-ℚ q<r)
                ( H r (leq-real-is-in-lower-cut-macneille-ℝ x r<x))))
```

### Strict inequality of MacNeille real numbers at a universe level is a strict order

```agda
strict-preorder-macneille-ℝ : (l : Level) → Strict-Preorder (lsuc l) l
strict-preorder-macneille-ℝ l =
  ( macneille-ℝ l ,
    le-prop-macneille-ℝ ,
    irreflexive-le-macneille-ℝ ,
    transitive-le-macneille-ℝ)

abstract
  extensionality-strict-preorder-macneille-ℝ :
    (l : Level) →
    extensionality-principle-Strict-Preorder
      ( strict-preorder-macneille-ℝ l)
  extensionality-strict-preorder-macneille-ℝ l x y (_ , x~y) =
    eq-sim-macneille-ℝ
      ( sim-le-same-rational-macneille-ℝ x y
        ( λ q →
          ( inv-iff
            ( le-iff-le-right-raise-macneille-ℝ l y (macneille-real-ℚ q))) ∘iff
          ( x~y (raise-macneille-ℝ l (macneille-real-ℚ q))) ∘iff
          ( le-iff-le-right-raise-macneille-ℝ l x (macneille-real-ℚ q))))

strict-order-macneille-ℝ : (l : Level) → Strict-Order (lsuc l) l
strict-order-macneille-ℝ l =
  ( strict-preorder-macneille-ℝ l ,
    extensionality-strict-preorder-macneille-ℝ l)
```
