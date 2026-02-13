# Addition of MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.addition-lower-dedekind-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.addition-upper-dedekind-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.arithmetically-located-macneille-real-numbers
open import real-numbers.located-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.negation-macneille-real-numbers
open import real-numbers.raising-universe-levels-located-macneille-real-numbers
open import real-numbers.raising-universe-levels-macneille-real-numbers
open import real-numbers.rational-lower-dedekind-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-macneille-real-numbers
open import real-numbers.strict-inequality-macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
open import real-numbers.zero-macneille-real-numbers
```

</details>

## Idea

We introduce
{{#concept "addition" Disambiguation="MacNeille real numbers" Agda=add-macneille-ℝ}}
on the [MacNeille real numbers](real-numbers.macneille-real-numbers.md) and
derive its basic properties.

The sum of two MacNeille real numbers is a real number whose lower cut (upper
cut) is the
[Minkowski sum](group-theory.minkowski-multiplication-commutative-monoids.md) of
their lower (upper) cuts. When either of the summands is located then this real
number again forms a MacNeille real number. By convention, we assume the left
summand is located.

## Definitions

### The underlying cuts of a sum of MacNeille real numbers

```agda
lower-real-add-macneille-ℝ :
  {l1 l2 : Level} → macneille-ℝ l1 → macneille-ℝ l2 → lower-ℝ (l1 ⊔ l2)
lower-real-add-macneille-ℝ x y =
  add-lower-ℝ (lower-real-macneille-ℝ x) (lower-real-macneille-ℝ y)

upper-real-add-macneille-ℝ :
  {l1 l2 : Level} → macneille-ℝ l1 → macneille-ℝ l2 → upper-ℝ (l1 ⊔ l2)
upper-real-add-macneille-ℝ x y =
  add-upper-ℝ (upper-real-macneille-ℝ x) (upper-real-macneille-ℝ y)
```

Openness of upper cut.

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  abstract
    forward-is-open-upper-complement-lower-cut-add-macneille-ℝ :
      (q : ℚ) →
      is-in-cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q →
      exists
        ( ℚ)
        ( λ p →
          le-ℚ-Prop p q ∧ ¬' cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p)
    forward-is-open-upper-complement-lower-cut-add-macneille-ℝ q q<x+y =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ℚ
              ( λ p →
                le-ℚ-Prop p q ∧
                ¬' cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p))
      in do
        ((ux , uy) , x<ux , y<uy , q=ux+uy) ← q<x+y
        (px , px<ux , px∉x) ←
          forward-implication
            ( is-open-upper-complement-lower-cut-macneille-ℝ x ux)
            ( x<ux)
        intro-exists
          ( px +ℚ uy)
          ( ( inv-tr
              ( le-ℚ (px +ℚ uy))
              ( q=ux+uy)
              ( preserves-le-left-add-ℚ uy px ux px<ux)) ,
            ( elim-exists
              ( empty-Prop)
              ( λ (lx , ly) (lx<x , ly<y , p=lx+ly) →
                px∉x
                  ( le-lower-cut-macneille-ℝ x
                    ( reflects-le-left-add-ℚ
                      ( ly)
                      ( px)
                      ( lx)
                      ( tr
                        ( le-ℚ (px +ℚ ly))
                        ( p=lx+ly)
                        ( preserves-le-right-add-ℚ
                          ( px)
                          ( ly)
                          ( uy)
                          ( le-lower-upper-cut-macneille-ℝ y ly<y y<uy))))
                    ( lx<x)))))

    backward-is-open-upper-complement-lower-cut-add-is-arithmetically-located-left-macneille-ℝ' :
      is-arithmetically-located-macneille-ℝ x →
      (p q : ℚ) →
      le-ℚ p q →
      ¬ is-in-cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p →
      is-in-cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q
    backward-is-open-upper-complement-lower-cut-add-is-arithmetically-located-left-macneille-ℝ'
      is-arithmetically-located-x p q p<q p∉x+y =
      let
        open
          do-syntax-trunc-Prop
            ( cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q)
      in do
        ((a , b) , b<a+ε , a<x , x<b) ←
          is-arithmetically-located-x (positive-diff-le-ℚ p<q)
        (a' , a<a' , a'<x) ←
          forward-implication
            ( is-rounded-lower-cut-macneille-ℝ x a)
            ( a<x)
        let
          p-a'<p-a : le-ℚ (p -ℚ a') (p -ℚ a)
          p-a'<p-a =
            preserves-le-right-add-ℚ
              ( p)
              ( neg-ℚ a')
              ( neg-ℚ a)
              ( neg-le-ℚ a<a')

          p-a'∉y : ¬ is-in-cut-lower-ℝ (lower-real-macneille-ℝ y) (p -ℚ a')
          p-a'∉y p-a'<y =
            p∉x+y
              ( intro-exists
                ( a' , p -ℚ a')
                ( a'<x ,
                  p-a'<y ,
                  inv (is-identity-right-conjugation-add-ℚ a' p)))

          y<p-a : is-in-cut-upper-ℝ (upper-real-macneille-ℝ y) (p -ℚ a)
          y<p-a =
            backward-implication
              ( is-open-upper-complement-lower-cut-macneille-ℝ y (p -ℚ a))
              ( intro-exists (p -ℚ a') (p-a'<p-a , p-a'∉y))

          p-a<q-b : le-ℚ (p -ℚ a) (q -ℚ b)
          p-a<q-b = le-triple-transpose-right-add-diff-ℚ p q a b b<a+ε

          y<q-b : is-in-cut-upper-ℝ (upper-real-macneille-ℝ y) (q -ℚ b)
          y<q-b =
            le-upper-cut-macneille-ℝ
              ( y)
              ( p-a<q-b)
              ( y<p-a)
        intro-exists
          ( b , q -ℚ b)
          ( x<b , y<q-b , inv (is-identity-right-conjugation-add-ℚ b q))

    backward-is-open-upper-complement-lower-cut-add-is-arithmetically-located-left-macneille-ℝ :
      is-arithmetically-located-macneille-ℝ x →
      (q : ℚ) →
      exists
        ( ℚ)
        ( λ p →
          le-ℚ-Prop p q ∧ ¬' cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p) →
      is-in-cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q
    backward-is-open-upper-complement-lower-cut-add-is-arithmetically-located-left-macneille-ℝ
      is-arithmetically-located-x q =
      elim-exists
        ( cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q)
        ( λ p (p<q , p∉x+y) →
          backward-is-open-upper-complement-lower-cut-add-is-arithmetically-located-left-macneille-ℝ'
            ( is-arithmetically-located-x)
            ( p)
            ( q)
            ( p<q)
            ( p∉x+y))

    is-open-upper-complement-lower-cut-add-is-arithmetically-located-left-macneille-ℝ :
      is-arithmetically-located-macneille-ℝ x →
      (q : ℚ) →
      is-in-cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q ↔
      exists
        ( ℚ)
        ( λ p →
          le-ℚ-Prop p q ∧ ¬' cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p)
    is-open-upper-complement-lower-cut-add-is-arithmetically-located-left-macneille-ℝ
      is-arithmetically-located-x q =
      ( forward-is-open-upper-complement-lower-cut-add-macneille-ℝ q ,
        backward-is-open-upper-complement-lower-cut-add-is-arithmetically-located-left-macneille-ℝ
          ( is-arithmetically-located-x)
          ( q))
```

Openness of lower cut.

```agda
    forward-is-open-lower-complement-upper-cut-add-macneille-ℝ :
      (p : ℚ) →
      is-in-cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p →
      exists
        ( ℚ)
        ( λ q →
          le-ℚ-Prop p q ∧
          ¬' cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q)
    forward-is-open-lower-complement-upper-cut-add-macneille-ℝ p p<x+y =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ℚ
              ( λ q →
                le-ℚ-Prop p q ∧
                ¬' cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q))
      in do
        ((lx , ly) , lx<x , ly<y , p=lx+ly) ← p<x+y
        (qx , lx<qx , qx∉x) ←
          forward-implication
            ( is-open-lower-complement-upper-cut-macneille-ℝ x lx)
            ( lx<x)
        intro-exists
          ( qx +ℚ ly)
          ( ( inv-tr
              ( λ t → le-ℚ t (qx +ℚ ly))
              ( p=lx+ly)
              ( preserves-le-left-add-ℚ ly lx qx lx<qx)) ,
            ( elim-exists
              ( empty-Prop)
              ( λ (ux , uy) (x<ux , y<uy , q=ux+uy) →
                qx∉x
                  ( le-upper-cut-macneille-ℝ x
                    ( reflects-le-left-add-ℚ
                      ( ly)
                      ( ux)
                      ( qx)
                      ( tr
                        ( le-ℚ (ux +ℚ ly))
                        ( inv q=ux+uy)
                        ( preserves-le-right-add-ℚ
                          ( ux)
                          ( ly)
                          ( uy)
                          ( le-lower-upper-cut-macneille-ℝ y ly<y y<uy))))
                    ( x<ux)))))

    backward-is-open-lower-complement-upper-cut-add-is-arithmetically-located-left-macneille-ℝ' :
      is-arithmetically-located-macneille-ℝ x →
      (p q : ℚ) →
      le-ℚ p q →
      ¬ (is-in-cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q) →
      is-in-cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p
    backward-is-open-lower-complement-upper-cut-add-is-arithmetically-located-left-macneille-ℝ'
      is-arithmetically-located-x p q p<q q∉x+y =
      let
        open
          do-syntax-trunc-Prop
            ( cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p)
      in do
        ((a , b) , b<a+ε , a<x , x<b) ←
          is-arithmetically-located-x (positive-diff-le-ℚ p<q)
        let
          q-b∉y : ¬ is-in-cut-upper-ℝ (upper-real-macneille-ℝ y) (q -ℚ b)
          q-b∉y q-b<y =
            q∉x+y
              ( intro-exists
                ( b , q -ℚ b)
                ( x<b , q-b<y , inv (is-identity-right-conjugation-add-ℚ b q)))

          p-a<q-b : le-ℚ (p -ℚ a) (q -ℚ b)
          p-a<q-b =
            le-triple-transpose-right-add-diff-ℚ
              ( p)
              ( q)
              ( a)
              ( b)
              ( b<a+ε)

          p-a<y : is-in-cut-lower-ℝ (lower-real-macneille-ℝ y) (p -ℚ a)
          p-a<y =
            backward-implication
              ( is-open-lower-complement-upper-cut-macneille-ℝ y (p -ℚ a))
              ( intro-exists (q -ℚ b) (p-a<q-b , q-b∉y))
        intro-exists
          ( a , p -ℚ a)
          ( a<x , p-a<y , inv (is-identity-right-conjugation-add-ℚ a p))

    backward-is-open-lower-complement-upper-cut-add-is-arithmetically-located-left-macneille-ℝ :
      is-arithmetically-located-macneille-ℝ x →
      (p : ℚ) →
      exists
        ( ℚ)
        ( λ q →
          le-ℚ-Prop p q ∧ ¬' cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q) →
      is-in-cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p
    backward-is-open-lower-complement-upper-cut-add-is-arithmetically-located-left-macneille-ℝ
      is-arithmetically-located-x p =
      elim-exists
        ( cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p)
        ( λ q (p<q , q∉x+y) →
          backward-is-open-lower-complement-upper-cut-add-is-arithmetically-located-left-macneille-ℝ'
            ( is-arithmetically-located-x)
            ( p)
            ( q)
            ( p<q)
            ( q∉x+y))

    is-open-lower-complement-upper-cut-add-is-arithmetically-located-left-macneille-ℝ :
      is-arithmetically-located-macneille-ℝ x →
      (p : ℚ) →
      is-in-cut-lower-ℝ (lower-real-add-macneille-ℝ x y) p ↔
      exists
        ( ℚ)
        ( λ q →
          le-ℚ-Prop p q ∧ ¬' cut-upper-ℝ (upper-real-add-macneille-ℝ x y) q)
    is-open-lower-complement-upper-cut-add-is-arithmetically-located-left-macneille-ℝ
      is-arithmetically-located-x p =
      ( forward-is-open-lower-complement-upper-cut-add-macneille-ℝ p ,
      backward-is-open-lower-complement-upper-cut-add-is-arithmetically-located-left-macneille-ℝ
        ( is-arithmetically-located-x)
        ( p))

    is-open-dedekind-macneille-add-is-arithmetically-located-left-macneille-ℝ :
      is-arithmetically-located-macneille-ℝ x →
      is-open-dedekind-macneille-lower-upper-ℝ
        ( lower-real-add-macneille-ℝ x y)
        ( upper-real-add-macneille-ℝ x y)
    is-open-dedekind-macneille-add-is-arithmetically-located-left-macneille-ℝ
      is-arithmetically-located-x =
      ( is-open-upper-complement-lower-cut-add-is-arithmetically-located-left-macneille-ℝ
          ( is-arithmetically-located-x) ,
        is-open-lower-complement-upper-cut-add-is-arithmetically-located-left-macneille-ℝ
          ( is-arithmetically-located-x))
```

### Addition between a located MacNeille real with a MacNeille real

```agda
is-open-dedekind-macneille-add-macneille-ℝ-left-located :
  {l1 l2 : Level} (x : located-macneille-ℝ l1) (y : macneille-ℝ l2) →
  is-open-dedekind-macneille-lower-upper-ℝ
    ( lower-real-add-macneille-ℝ (pr1 x) y)
    ( upper-real-add-macneille-ℝ (pr1 x) y)
is-open-dedekind-macneille-add-macneille-ℝ-left-located x y =
  is-open-dedekind-macneille-add-is-arithmetically-located-left-macneille-ℝ
    ( pr1 x)
    ( y)
    ( is-arithmetically-located-ℝ (real-macneille-ℝ (pr1 x) (pr2 x)))

opaque
  add-macneille-ℝ :
    {l1 l2 : Level} →
    located-macneille-ℝ l1 → macneille-ℝ l2 → macneille-ℝ (l1 ⊔ l2)
  add-macneille-ℝ x y =
    ( ( lower-real-add-macneille-ℝ (pr1 x) y ,
        upper-real-add-macneille-ℝ (pr1 x) y) ,
      is-open-dedekind-macneille-add-macneille-ℝ-left-located x y)

abstract opaque
  unfolding add-macneille-ℝ

  ap-add-macneille-ℝ :
    {l1 : Level} {x x' : located-macneille-ℝ l1} → (x ＝ x') →
    {l2 : Level} {y y' : macneille-ℝ l2} → (y ＝ y') →
    (add-macneille-ℝ x y) ＝ (add-macneille-ℝ x' y')
  ap-add-macneille-ℝ {x = x} {x' = x'} x=x' {y = y} {y' = y'} y=y' =
    eq-eq-lower-real-macneille-ℝ
      ( add-macneille-ℝ x y)
      ( add-macneille-ℝ x' y')
      ( ap-binary lower-real-add-macneille-ℝ (ap pr1 x=x') y=y')
```

## Properties

### Unit laws for addition

```agda
abstract opaque
  unfolding add-macneille-ℝ

  left-unit-law-add-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) →
    add-macneille-ℝ located-zero-macneille-ℝ x ＝ x
  left-unit-law-add-macneille-ℝ x =
    eq-eq-lower-real-macneille-ℝ
      ( add-macneille-ℝ located-zero-macneille-ℝ x)
      ( x)
      ( tr
        ( λ z →
          add-lower-ℝ z (lower-real-macneille-ℝ x) ＝ lower-real-macneille-ℝ x)
        ( inv (eq-lower-real-real-ℚ zero-ℚ))
        ( left-unit-law-add-lower-ℝ (lower-real-macneille-ℝ x)))
```

### Addition on the MacNeille real numbers preserves similarity

```agda
module _
  {l1 l2 l3 : Level}
  (z : macneille-ℝ l1)
  (x : located-macneille-ℝ l2)
  (y : located-macneille-ℝ l3)
  where

  abstract opaque
    unfolding add-macneille-ℝ sim-macneille-ℝ

    preserves-sim-right-add-macneille-ℝ :
      sim-macneille-ℝ (pr1 x) (pr1 y) →
      sim-macneille-ℝ (add-macneille-ℝ x z) (add-macneille-ℝ y z)
    pr1 (preserves-sim-right-add-macneille-ℝ (lx⊆ly , _)) q =
      map-tot-exists (λ (qx , _) → map-product (lx⊆ly qx) id)
    pr2 (preserves-sim-right-add-macneille-ℝ (_ , ly⊆lx)) q =
      map-tot-exists (λ (qy , _) → map-product (ly⊆lx qy) id)

module _
  {l1 l2 l3 : Level}
  (z : located-macneille-ℝ l1)
  (x : macneille-ℝ l2)
  (y : macneille-ℝ l3)
  where

  abstract opaque
    unfolding add-macneille-ℝ sim-macneille-ℝ

    preserves-sim-left-add-macneille-ℝ :
      sim-macneille-ℝ x y →
      sim-macneille-ℝ (add-macneille-ℝ z x) (add-macneille-ℝ z y)
    pr1 (preserves-sim-left-add-macneille-ℝ (lx⊆ly , _)) q =
      map-tot-exists (λ (qz , qx) → map-product id (map-product (lx⊆ly qx) id))
    pr2 (preserves-sim-left-add-macneille-ℝ (_ , ly⊆lx)) q =
      map-tot-exists (λ (qz , qy) → map-product id (map-product (ly⊆lx qy) id))

abstract
  preserves-sim-add-macneille-ℝ :
    {l1 l2 l3 l4 : Level}
    {x : located-macneille-ℝ l1}
    {x' : located-macneille-ℝ l2}
    {y : macneille-ℝ l3}
    {y' : macneille-ℝ l4} →
    sim-macneille-ℝ (pr1 x) (pr1 x') →
    sim-macneille-ℝ y y' →
    sim-macneille-ℝ (add-macneille-ℝ x y) (add-macneille-ℝ x' y')
  preserves-sim-add-macneille-ℝ {x = x} {x'} {y} {y'} x~x' y~y' =
    transitive-sim-macneille-ℝ
      ( add-macneille-ℝ x y)
      ( add-macneille-ℝ x' y)
      ( add-macneille-ℝ x' y')
      ( preserves-sim-left-add-macneille-ℝ x' y y' y~y')
      ( preserves-sim-right-add-macneille-ℝ y x x' x~x')
```

### Raised unit laws for addition

```agda
abstract
  left-raise-zero-law-add-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) →
    add-macneille-ℝ (raise-zero-located-macneille-ℝ l) x ＝ x
  left-raise-zero-law-add-macneille-ℝ {l} x =
    eq-sim-macneille-ℝ
      ( transitive-sim-macneille-ℝ _ _ _
        ( sim-eq-macneille-ℝ (left-unit-law-add-macneille-ℝ x))
        ( preserves-sim-right-add-macneille-ℝ
          ( x)
          ( raise-zero-located-macneille-ℝ l)
          ( located-zero-macneille-ℝ)
          ( sim-raise-zero-macneille-ℝ)))
```

### Raising the universe level distributes over addition

```agda
abstract
  distributive-raise-add-macneille-ℝ :
    {l1 l2 : Level} (l3 : Level) →
    (x : located-macneille-ℝ l1)
    (y : macneille-ℝ l2) →
    raise-macneille-ℝ l3 (add-macneille-ℝ x y) ＝
    add-macneille-ℝ
      ( located-raise-macneille-ℝ l3 x)
      ( raise-macneille-ℝ l3 y)
  distributive-raise-add-macneille-ℝ l3 x y =
    eq-sim-macneille-ℝ
      ( similarity-reasoning-macneille-ℝ
        raise-macneille-ℝ l3 (add-macneille-ℝ x y)
        ~ℝₘ add-macneille-ℝ x y
          by sim-raise-macneille-ℝ' l3 (add-macneille-ℝ x y)
        ~ℝₘ
        add-macneille-ℝ
          ( located-raise-macneille-ℝ l3 x)
          ( raise-macneille-ℝ l3 y)
          by
            preserves-sim-add-macneille-ℝ
              {x = x}
              {x' = located-raise-macneille-ℝ l3 x}
              {y = y}
              {y' = raise-macneille-ℝ l3 y}
              ( sim-raise-macneille-ℝ l3 (pr1 x))
              ( sim-raise-macneille-ℝ l3 y))
```

### The inclusion of rational numbers preserves addition

```agda
abstract opaque
  unfolding add-macneille-ℝ

  add-macneille-real-ℚ :
    (p q : ℚ) →
    add-macneille-ℝ (located-macneille-real-ℚ p) (macneille-real-ℚ q) ＝
    macneille-real-ℚ (p +ℚ q)
  add-macneille-real-ℚ p q =
    eq-eq-lower-real-macneille-ℝ
      ( add-macneille-ℝ (located-macneille-real-ℚ p) (macneille-real-ℚ q))
      ( macneille-real-ℚ (p +ℚ q))
      ( ( ap-binary add-lower-ℝ
          ( eq-lower-real-macneille-real-ℚ p)
          ( eq-lower-real-macneille-real-ℚ q)) ∙
        ( add-lower-real-ℚ p q) ∙
        ( inv (eq-lower-real-macneille-real-ℚ (p +ℚ q))))
```

### The inclusion of integers preserves addition

```agda
abstract
  add-macneille-real-ℤ :
    (x y : ℤ) →
    add-macneille-ℝ (located-macneille-real-ℤ x) (macneille-real-ℤ y) ＝
    macneille-real-ℤ (x +ℤ y)
  add-macneille-real-ℤ x y =
    equational-reasoning
      add-macneille-ℝ (located-macneille-real-ℤ x) (macneille-real-ℤ y)
      ＝ macneille-real-ℚ (rational-ℤ x +ℚ rational-ℤ y)
        by add-macneille-real-ℚ _ _
      ＝ macneille-real-ℤ (x +ℤ y)
        by ap macneille-real-ℚ (add-rational-ℤ x y)
```

### The inclusion of natural numbers preserves addition

```agda
abstract
  add-macneille-real-ℕ :
    (x y : ℕ) →
    add-macneille-ℝ (located-macneille-real-ℕ x) (macneille-real-ℕ y) ＝
    macneille-real-ℕ (x +ℕ y)
  add-macneille-real-ℕ x y =
    equational-reasoning
      add-macneille-ℝ (located-macneille-real-ℕ x) (macneille-real-ℕ y)
      ＝ macneille-real-ℤ (int-ℕ x +ℤ int-ℕ y)
        by add-macneille-real-ℤ _ _
      ＝ macneille-real-ℕ (x +ℕ y)
        by ap macneille-real-ℤ (add-int-ℕ x y)
```

### `½ + ½ = 1`

```agda
abstract
  twice-one-half-macneille-ℝ :
    add-macneille-ℝ
      ( located-macneille-real-ℚ one-half-ℚ)
      ( one-half-macneille-ℝ) ＝
    one-macneille-ℝ
  twice-one-half-macneille-ℝ =
    add-macneille-real-ℚ _ _ ∙ ap macneille-real-ℚ twice-one-half-ℚ
```

### Adding raised MacNeille real numbers

```agda
abstract
  associative-add-macneille-ℝ :
    {l1 l2 l3 : Level}
    (x : located-macneille-ℝ l1)
    (y : located-macneille-ℝ l2)
    (z : macneille-ℝ l3) →
    add-lower-ℝ
      ( lower-real-macneille-ℝ (pr1 x))
      ( add-lower-ℝ
        ( lower-real-macneille-ℝ (pr1 y))
        ( lower-real-macneille-ℝ z)) ＝
    add-lower-ℝ
      ( add-lower-ℝ
        ( lower-real-macneille-ℝ (pr1 x))
        ( lower-real-macneille-ℝ (pr1 y)))
      ( lower-real-macneille-ℝ z)
  associative-add-macneille-ℝ x y z =
    inv
      ( associative-add-lower-ℝ
        ( lower-real-macneille-ℝ (pr1 x))
        ( lower-real-macneille-ℝ (pr1 y))
        ( lower-real-macneille-ℝ z))

abstract
  add-raise-macneille-ℝ :
    {l1 l2 l3 l4 : Level}
    {x : located-macneille-ℝ l1}
    {y : macneille-ℝ l2} →
    add-macneille-ℝ
      ( located-raise-macneille-ℝ l3 x)
      ( raise-macneille-ℝ l4 y) ＝
    raise-macneille-ℝ (l3 ⊔ l4) (add-macneille-ℝ x y)
  add-raise-macneille-ℝ {l3 = l3} {l4 = l4} {x = x} {y = y} =
    eq-sim-macneille-ℝ
      ( similarity-reasoning-macneille-ℝ
        add-macneille-ℝ
          ( located-raise-macneille-ℝ l3 x)
          ( raise-macneille-ℝ l4 y)
        ~ℝₘ add-macneille-ℝ x y
          by
            preserves-sim-add-macneille-ℝ
              {x = located-raise-macneille-ℝ l3 x}
              {x' = x}
              {y = raise-macneille-ℝ l4 y}
              {y' = y}
              ( sim-raise-macneille-ℝ' l3 (pr1 x))
              ( sim-raise-macneille-ℝ' l4 y)
        ~ℝₘ raise-macneille-ℝ (l3 ⊔ l4) (add-macneille-ℝ x y)
          by sim-raise-macneille-ℝ (l3 ⊔ l4) (add-macneille-ℝ x y))
```

## See also

- In
  [The addition isometry on real numbers](real-numbers.isometry-addition-real-numbers.md)
  we show that addition is an
  [isometry](metric-spaces.isometries-metric-spaces.md) from the
  [metric space of real numbers](real-numbers.metric-space-of-real-numbers.md)
  to the
  [metric space of isometries](metric-spaces.metric-space-of-isometries-metric-spaces.md)
  of `ℝ`.
