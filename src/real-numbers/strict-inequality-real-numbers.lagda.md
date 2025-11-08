# Strict inequality of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-disjunction
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="real numbers" Agda=le-ℝ}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) is defined as the
presence of a [rational number](elementary-number-theory.rational-numbers.md)
between them. This is the definition used in {{#cite UF13}}, section 11.2.1.

```agda
opaque
  le-ℝ : Large-Relation _⊔_ ℝ
  le-ℝ x y = exists ℚ (λ q → upper-cut-ℝ x q ∧ lower-cut-ℝ y q)

  is-prop-le-ℝ : {l1 l2 : Level} → (x : ℝ l1) (y : ℝ l2) → is-prop (le-ℝ x y)
  is-prop-le-ℝ x y = is-prop-exists ℚ (λ q → upper-cut-ℝ x q ∧ lower-cut-ℝ y q)

le-prop-ℝ : Large-Relation-Prop _⊔_ ℝ
le-prop-ℝ x y = (le-ℝ x y , is-prop-le-ℝ x y)
```

## Properties

### Strict inequality on the reals implies inequality

```agda
abstract opaque
  unfolding le-ℝ leq-ℝ

  leq-le-ℝ : {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → le-ℝ x y → leq-ℝ x y
  leq-le-ℝ {x = x} {y = y} x<y p p<x =
    elim-exists
      ( lower-cut-ℝ y p)
      ( λ q (x<q , q<y) → le-lower-cut-ℝ y (le-lower-upper-cut-ℝ x p<x x<q) q<y)
      ( x<y)
```

### Strict inequality on the reals is irreflexive

```agda
abstract opaque
  unfolding le-ℝ

  irreflexive-le-ℝ : {l : Level} (x : ℝ l) → ¬ (le-ℝ x x)
  irreflexive-le-ℝ x =
    elim-exists
      ( empty-Prop)
      ( λ q (x<q , q<x) → is-disjoint-cut-ℝ x q (q<x , x<q))
```

### Strict inequality on the reals is asymmetric

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2}
  where

  abstract opaque
    unfolding le-ℝ

    asymmetric-le-ℝ : le-ℝ x y → ¬ (le-ℝ y x)
    asymmetric-le-ℝ x<y y<x =
      let
        open do-syntax-trunc-Prop empty-Prop
      in do
        ( p , x<p , p<y) ← x<y
        ( q , y<q , q<x) ← y<x
        rec-coproduct
          ( asymmetric-le-ℚ
            ( q)
            ( p)
            ( le-lower-upper-cut-ℝ x q<x x<p))
          ( not-leq-le-ℚ
            ( p)
            ( q)
            ( le-lower-upper-cut-ℝ y p<y y<q))
          ( decide-le-leq-ℚ p q)
```

### Strict inequality on the reals is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  abstract opaque
    unfolding le-ℝ

    transitive-le-ℝ : le-ℝ y z → le-ℝ x y → le-ℝ x z
    transitive-le-ℝ y<z x<y =
      let
        open do-syntax-trunc-Prop (le-prop-ℝ x z)
      in do
        ( p , x<p , p<y) ← x<y
        ( q , y<q , q<z) ← y<z
        intro-exists
          ( p)
          ( x<p , le-lower-cut-ℝ z (le-lower-upper-cut-ℝ y p<y y<q) q<z)
```

### The canonical map from rationals to reals preserves and reflects strict inequality

```agda
module _
  {x y : ℚ}
  where

  abstract opaque
    unfolding le-ℝ real-ℚ

    preserves-le-real-ℚ : le-ℚ x y → le-ℝ (real-ℚ x) (real-ℚ y)
    preserves-le-real-ℚ = dense-le-ℚ

    reflects-le-real-ℚ : le-ℝ (real-ℚ x) (real-ℚ y) → le-ℚ x y
    reflects-le-real-ℚ =
      elim-exists
        ( le-ℚ-Prop x y)
        ( λ q (x<q , q<y) → transitive-le-ℚ x q y q<y x<q)

  iff-le-real-ℚ : le-ℚ x y ↔ le-ℝ (real-ℚ x) (real-ℚ y)
  pr1 iff-le-real-ℚ = preserves-le-real-ℚ
  pr2 iff-le-real-ℚ = reflects-le-real-ℚ
```

### Concatenation rules for inequality and strict inequality on the real numbers

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  abstract opaque
    unfolding le-ℝ leq-ℝ leq-ℝ'

    concatenate-le-leq-ℝ : le-ℝ x y → leq-ℝ y z → le-ℝ x z
    concatenate-le-leq-ℝ x<y y≤z =
      map-tot-exists (λ p → map-product id (y≤z p)) x<y

    concatenate-leq-le-ℝ : leq-ℝ x y → le-ℝ y z → le-ℝ x z
    concatenate-leq-le-ℝ x≤y =
      map-tot-exists
        ( λ p → map-product (forward-implication (leq-iff-ℝ' x y) x≤y p) id)
```

### A rational is in the lower cut of `x` iff its real projection is less than `x`

```agda
module _
  {l : Level} {q : ℚ} (x : ℝ l)
  where

  abstract opaque
    unfolding le-ℝ real-ℚ

    le-real-iff-lower-cut-ℚ : is-in-lower-cut-ℝ x q ↔ le-ℝ (real-ℚ q) x
    le-real-iff-lower-cut-ℚ = is-rounded-lower-cut-ℝ x q

    le-real-is-in-lower-cut-ℚ : is-in-lower-cut-ℝ x q → le-ℝ (real-ℚ q) x
    le-real-is-in-lower-cut-ℚ = forward-implication le-real-iff-lower-cut-ℚ

    is-in-lower-cut-le-real-ℚ : le-ℝ (real-ℚ q) x → is-in-lower-cut-ℝ x q
    is-in-lower-cut-le-real-ℚ = backward-implication le-real-iff-lower-cut-ℚ
```

### A rational is in the upper cut of `x` iff its real projection is greater than `x`

```agda
module _
  {l : Level} {q : ℚ} (x : ℝ l)
  where

  abstract opaque
    unfolding le-ℝ real-ℚ

    le-iff-upper-cut-real-ℚ : is-in-upper-cut-ℝ x q ↔ le-ℝ x (real-ℚ q)
    le-iff-upper-cut-real-ℚ =
      iff-tot-exists (λ _ → iff-equiv commutative-product) ∘iff
      is-rounded-upper-cut-ℝ x q

    le-real-is-in-upper-cut-ℚ : is-in-upper-cut-ℝ x q → le-ℝ x (real-ℚ q)
    le-real-is-in-upper-cut-ℚ = forward-implication le-iff-upper-cut-real-ℚ

    is-in-upper-cut-le-real-ℚ : le-ℝ x (real-ℚ q) → is-in-upper-cut-ℝ x q
    is-in-upper-cut-le-real-ℚ = backward-implication le-iff-upper-cut-real-ℚ
```

### The real numbers are located

```agda
module _
  {l : Level} (x : ℝ l) (p q : ℚ) (p<q : le-ℚ p q)
  where

  abstract
    is-located-le-ℝ : disjunction-type (le-ℝ (real-ℚ p) x) (le-ℝ x (real-ℚ q))
    is-located-le-ℝ =
      map-disjunction
        ( le-real-is-in-lower-cut-ℚ x)
        ( le-real-is-in-upper-cut-ℚ x)
        ( is-located-lower-upper-cut-ℝ x p<q)
```

### Every real is less than a rational number

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
    le-some-rational-ℝ : exists ℚ (λ q → le-prop-ℝ x (real-ℚ q))
    le-some-rational-ℝ =
      map-tot-exists
        ( λ q → le-real-is-in-upper-cut-ℚ x)
        ( is-inhabited-upper-cut-ℝ x)
```

### The reals have no lower or upper bound

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  abstract
    exists-lesser-ℝ : exists (ℝ lzero) (λ y → le-prop-ℝ y x)
    exists-lesser-ℝ =
      let
        open do-syntax-trunc-Prop (∃ (ℝ lzero) (λ y → le-prop-ℝ y x))
      in do
        ( q , q<x) ← is-inhabited-lower-cut-ℝ x
        intro-exists (real-ℚ q) (le-real-is-in-lower-cut-ℚ x q<x)

    exists-greater-ℝ : exists (ℝ lzero) (λ y → le-prop-ℝ x y)
    exists-greater-ℝ =
      let
        open do-syntax-trunc-Prop (∃ (ℝ lzero) (le-prop-ℝ x))
      in do
        ( q , x<q) ← is-inhabited-upper-cut-ℝ x
        intro-exists (real-ℚ q) (le-real-is-in-upper-cut-ℚ x x<q)
```

### Negation reverses the strict ordering of real numbers

```agda
module _
  {l1 l2 : Level}
  {x : ℝ l1} {y : ℝ l2}
  where

  abstract opaque
    unfolding le-ℝ neg-ℝ

    neg-le-ℝ : le-ℝ x y → le-ℝ (neg-ℝ y) (neg-ℝ x)
    neg-le-ℝ x<y =
      let
        open do-syntax-trunc-Prop (le-prop-ℝ (neg-ℝ y) (neg-ℝ x))
      in do
        (p , x<p , p<y) ← x<y
        intro-exists
          ( neg-ℚ p)
          ( inv-tr (is-in-lower-cut-ℝ y) (neg-neg-ℚ p) p<y ,
            inv-tr (is-in-upper-cut-ℝ x) (neg-neg-ℚ p) x<p)
```

### If `x` is less than `y`, then `y` is not less than or equal to `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract opaque
    unfolding le-ℝ leq-ℝ

    not-leq-le-ℝ : le-ℝ x y → ¬ (leq-ℝ y x)
    not-leq-le-ℝ x<y y≤x =
      elim-exists
        ( empty-Prop)
        ( λ q (x<q , q<y) → is-disjoint-cut-ℝ x q (y≤x q q<y , x<q))
        ( x<y)
```

### If `x` is not less than `y`, then `y` is less than or equal to `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract opaque
    unfolding le-ℝ leq-ℝ

    leq-not-le-ℝ : ¬ (le-ℝ x y) → leq-ℝ y x
    leq-not-le-ℝ x≮y p p<y =
      let
        open do-syntax-trunc-Prop (lower-cut-ℝ x p)
      in do
        ( q , p<q , q<y) ←
          forward-implication (is-rounded-lower-cut-ℝ y p) p<y
        elim-disjunction
          ( lower-cut-ℝ x p)
          ( id)
          ( λ x<q → reductio-ad-absurdum (intro-exists q (x<q , q<y)) x≮y)
          ( is-located-lower-upper-cut-ℝ x p<q)
```

### If `x` is less than or equal to `y`, then `y` is not less than `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  not-le-leq-ℝ : leq-ℝ x y → ¬ (le-ℝ y x)
  not-le-leq-ℝ x≤y y<x = not-leq-le-ℝ y x y<x x≤y
```

### `x` is less than or equal to `y` if and only if `y` is not less than `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-iff-not-le-ℝ : leq-ℝ x y ↔ ¬ (le-ℝ y x)
  pr1 leq-iff-not-le-ℝ = not-le-leq-ℝ x y
  pr2 leq-iff-not-le-ℝ = leq-not-le-ℝ y x
```

### The rational numbers are dense in the real numbers

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  abstract opaque
    unfolding le-ℝ

    dense-rational-le-ℝ :
      le-ℝ x y →
      exists ℚ (λ z → le-prop-ℝ x (real-ℚ z) ∧ le-prop-ℝ (real-ℚ z) y)
    dense-rational-le-ℝ =
      map-tot-exists
        ( λ q →
          map-product
            ( le-real-is-in-upper-cut-ℚ x)
            ( le-real-is-in-lower-cut-ℚ y))
```

### Strict inequality on the real numbers is dense

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  abstract
    dense-le-ℝ :
      le-ℝ x y → exists (ℝ lzero) (λ z → le-prop-ℝ x z ∧ le-prop-ℝ z y)
    dense-le-ℝ x<y =
      map-exists
        ( _)
        ( real-ℚ)
        ( λ _ → id)
        ( dense-rational-le-ℝ x y x<y)
```

### Strict inequality on the real numbers is cotransitive

```agda
abstract opaque
  unfolding le-ℝ

  cotransitive-le-ℝ : is-cotransitive-Large-Relation-Prop ℝ le-prop-ℝ
  cotransitive-le-ℝ x y z x<y =
    let
      open do-syntax-trunc-Prop (le-prop-ℝ x z ∨ le-prop-ℝ z y)
    in do
      ( q , x<q , q<y) ← x<y
      ( p , p<q , x<p) ← forward-implication (is-rounded-upper-cut-ℝ x q) x<q
      map-disjunction
        ( λ p<z → intro-exists p (x<p , p<z))
        ( λ z<q → intro-exists q (z<q , q<y))
        ( is-located-lower-upper-cut-ℝ z p<q)
```

### Strict inequality on the real numbers is invariant under similarity

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) (x~y : sim-ℝ x y)
  where

  abstract opaque
    unfolding le-ℝ sim-ℝ

    preserves-le-left-sim-ℝ : le-ℝ x z → le-ℝ y z
    preserves-le-left-sim-ℝ =
      map-tot-exists
        ( λ q →
          map-product
            ( pr1 (sim-upper-cut-sim-ℝ x y x~y) q)
            ( id))

    preserves-le-right-sim-ℝ : le-ℝ z x → le-ℝ z y
    preserves-le-right-sim-ℝ =
      map-tot-exists ( λ q → map-product id (pr1 x~y q))

module _
  {l1 l2 l3 l4 : Level}
  {x1 : ℝ l1} {x2 : ℝ l2} {y1 : ℝ l3} {y2 : ℝ l4}
  (x1~x2 : sim-ℝ x1 x2) (y1~y2 : sim-ℝ y1 y2)
  where

  preserves-le-sim-ℝ : le-ℝ x1 y1 → le-ℝ x2 y2
  preserves-le-sim-ℝ x1<y1 =
    preserves-le-left-sim-ℝ
      ( y2)
      ( x1)
      ( x2)
      ( x1~x2)
      ( preserves-le-right-sim-ℝ x1 y1 y2 y1~y2 x1<y1)
```

### If `x` is less than each rational number `y` is less than, then `x ≤ y`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract opaque
    unfolding leq-ℝ'

    leq-le-rational-ℝ :
      ((q : ℚ) → le-ℝ y (real-ℚ q) → le-ℝ x (real-ℚ q)) → leq-ℝ x y
    leq-le-rational-ℝ H =
      leq-leq'-ℝ _ _
        ( λ q y<q →
          is-in-upper-cut-le-real-ℚ x
            ( H q (le-real-is-in-upper-cut-ℚ y y<q)))
```

### Two real numbers are similar if they are less than the same rational numbers

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    sim-le-same-rational-ℝ :
      ((q : ℚ) → le-ℝ x (real-ℚ q) ↔ le-ℝ y (real-ℚ q)) → sim-ℝ x y
    sim-le-same-rational-ℝ H =
      sim-sim-leq-ℝ
        ( leq-le-rational-ℝ x y (backward-implication ∘ H) ,
          leq-le-rational-ℝ y x (forward-implication ∘ H))
```

## References

{{#bibliography}}
