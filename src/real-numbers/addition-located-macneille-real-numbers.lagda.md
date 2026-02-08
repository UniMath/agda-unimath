# Addition of located MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-located-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-lower-dedekind-real-numbers
open import real-numbers.addition-macneille-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.located-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.negation-macneille-real-numbers
open import real-numbers.raising-universe-levels-located-macneille-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

We consider [addition](real-numbers.addition-macneille-real-numbers.md) on
[MacNeille real numbers](real-numbers.macneille-real-numbers.md) restricted to
[located MacNeille real numbers](real-numbers.located-macneille-real-numbers.md).

## Lemma

### The MacNeille sum of two located MacNeille reals is located

```agda
abstract opaque
  unfolding add-macneille-ℝ

  is-located-add-located-macneille-ℝ :
    {l1 l2 : Level}
    (x : located-macneille-ℝ l1)
    (y : located-macneille-ℝ l2) →
    is-located-macneille-ℝ (add-macneille-ℝ x (pr1 y))
  is-located-add-located-macneille-ℝ x y p q p<q =
    elim-exists
      ( cut-lower-ℝ (lower-real-add-macneille-ℝ (pr1 x) (pr1 y)) p ∨
        cut-upper-ℝ (upper-real-add-macneille-ℝ (pr1 x) (pr1 y)) q)
      ( λ (a , b) (b<a+ε , a<x , x<b) →
        map-disjunction
          ( λ p-a<y →
            intro-exists
              ( a , p -ℚ a)
              ( a<x , p-a<y , inv (is-identity-right-conjugation-add-ℚ a p)))
          ( λ y<q-b →
            intro-exists
              ( b , q -ℚ b)
              ( x<b , y<q-b , inv (is-identity-right-conjugation-add-ℚ b q)))
          ( pr2
            ( y)
            ( p -ℚ a)
            ( q -ℚ b)
            ( le-triple-transpose-right-add-diff-ℚ p q a b b<a+ε)))
      ( is-arithmetically-located-ℝ
        ( real-macneille-ℝ (pr1 x) (pr2 x))
        ( positive-diff-le-ℚ p<q))
```

## Definitions

### Addition of located MacNeille reals

```agda
add-located-macneille-ℝ :
  {l1 l2 : Level} →
  located-macneille-ℝ l1 →
  located-macneille-ℝ l2 →
  located-macneille-ℝ (l1 ⊔ l2)
add-located-macneille-ℝ x y =
  ( add-macneille-ℝ x (pr1 y) ,
    is-located-add-located-macneille-ℝ x y)

eq-add-located-macneille-ℝ :
  {l1 l2 : Level} {x x' : located-macneille-ℝ l1} →
  (x ＝ x') →
  {y y' : located-macneille-ℝ l2} →
  (y ＝ y') →
  add-located-macneille-ℝ x y ＝ add-located-macneille-ℝ x' y'
eq-add-located-macneille-ℝ {x = x} {x' = x'} x=x' {y = y} {y' = y'} y=y' =
  eq-type-subtype
    ( is-located-prop-macneille-ℝ)
    ( ap-add-macneille-ℝ x=x' (ap pr1 y=y'))
```

## Properties

### Addition is commutative

```agda
abstract opaque
  unfolding add-macneille-ℝ

  commutative-add-located-macneille-ℝ :
    {l1 l2 : Level}
    (x : located-macneille-ℝ l1)
    (y : located-macneille-ℝ l2) →
    add-located-macneille-ℝ x y ＝ add-located-macneille-ℝ y x
  commutative-add-located-macneille-ℝ x y =
    eq-type-subtype
      ( is-located-prop-macneille-ℝ)
      ( eq-eq-lower-real-macneille-ℝ
        ( add-macneille-ℝ x (pr1 y))
        ( add-macneille-ℝ y (pr1 x))
        ( commutative-add-lower-ℝ
          ( lower-real-macneille-ℝ (pr1 x))
          ( lower-real-macneille-ℝ (pr1 y))))
```

### Addition is associative

```agda
abstract opaque
  unfolding add-macneille-ℝ

  associative-add-located-macneille-ℝ :
    {l1 l2 l3 : Level}
    (x : located-macneille-ℝ l1)
    (y : located-macneille-ℝ l2)
    (z : located-macneille-ℝ l3) →
    add-located-macneille-ℝ (add-located-macneille-ℝ x y) z ＝
    add-located-macneille-ℝ x (add-located-macneille-ℝ y z)
  associative-add-located-macneille-ℝ x y z =
    eq-type-subtype
      ( is-located-prop-macneille-ℝ)
      ( eq-eq-lower-real-macneille-ℝ
        ( add-macneille-ℝ (add-located-macneille-ℝ x y) (pr1 z))
        ( add-macneille-ℝ x (pr1 (add-located-macneille-ℝ y z)))
        ( associative-add-lower-ℝ
          ( lower-real-macneille-ℝ (pr1 x))
          ( lower-real-macneille-ℝ (pr1 y))
          ( lower-real-macneille-ℝ (pr1 z))))
```

### Unit laws for addition

```agda
abstract opaque
  unfolding add-macneille-ℝ

  right-unit-law-add-located-macneille-ℝ :
    {l : Level} (x : located-macneille-ℝ l) →
    add-located-macneille-ℝ x located-zero-macneille-ℝ ＝ x
  right-unit-law-add-located-macneille-ℝ x =
    eq-type-subtype
      ( is-located-prop-macneille-ℝ)
      ( eq-eq-lower-real-macneille-ℝ
        ( add-macneille-ℝ x zero-macneille-ℝ)
        ( pr1 x)
        ( tr
          ( λ z →
            add-lower-ℝ (lower-real-macneille-ℝ (pr1 x)) z ＝
            lower-real-macneille-ℝ (pr1 x))
          ( inv (eq-lower-real-real-ℚ zero-ℚ))
          ( right-unit-law-add-lower-ℝ (lower-real-macneille-ℝ (pr1 x)))))
```

### Raised unit laws for addition

```agda
abstract
  right-raise-zero-law-add-located-macneille-ℝ :
    {l : Level} (x : located-macneille-ℝ l) →
    add-located-macneille-ℝ x (raise-zero-located-macneille-ℝ l) ＝ x
  right-raise-zero-law-add-located-macneille-ℝ {l} x =
    eq-type-subtype
      ( is-located-prop-macneille-ℝ)
      ( eq-sim-macneille-ℝ
        ( tr
          ( sim-macneille-ℝ (add-macneille-ℝ x (raise-zero-macneille-ℝ l)))
          ( ap pr1 (right-unit-law-add-located-macneille-ℝ x))
          ( preserves-sim-left-add-macneille-ℝ
            ( x)
            ( raise-zero-macneille-ℝ l)
            ( zero-macneille-ℝ)
            ( sim-raise-zero-macneille-ℝ))))
```

### Swapping laws for addition on located MacNeille real numbers

```agda
module _
  {l1 l2 l3 : Level}
  (x : located-macneille-ℝ l1)
  (y : located-macneille-ℝ l2)
  (z : located-macneille-ℝ l3)
  where

  abstract
    right-swap-add-located-macneille-ℝ :
      add-located-macneille-ℝ (add-located-macneille-ℝ x y) z ＝
      add-located-macneille-ℝ (add-located-macneille-ℝ x z) y
    right-swap-add-located-macneille-ℝ =
      equational-reasoning
        add-located-macneille-ℝ (add-located-macneille-ℝ x y) z
        ＝ add-located-macneille-ℝ x (add-located-macneille-ℝ y z)
          by associative-add-located-macneille-ℝ x y z
        ＝ add-located-macneille-ℝ x (add-located-macneille-ℝ z y)
          by
            ap
              ( add-located-macneille-ℝ x)
              ( commutative-add-located-macneille-ℝ y z)
        ＝ add-located-macneille-ℝ (add-located-macneille-ℝ x z) y
          by inv (associative-add-located-macneille-ℝ x z y)

    left-swap-add-located-macneille-ℝ :
      add-located-macneille-ℝ x (add-located-macneille-ℝ y z) ＝
      add-located-macneille-ℝ y (add-located-macneille-ℝ x z)
    left-swap-add-located-macneille-ℝ =
      equational-reasoning
        add-located-macneille-ℝ x (add-located-macneille-ℝ y z)
        ＝ add-located-macneille-ℝ (add-located-macneille-ℝ x y) z
          by inv (associative-add-located-macneille-ℝ x y z)
        ＝ add-located-macneille-ℝ (add-located-macneille-ℝ y x) z
          by
            eq-add-located-macneille-ℝ
              ( commutative-add-located-macneille-ℝ x y)
              refl
        ＝ add-located-macneille-ℝ y (add-located-macneille-ℝ x z)
          by associative-add-located-macneille-ℝ y x z
```

### Compatibility with addition on rationals

```agda
abstract
  add-located-macneille-real-ℚ :
    (p q : ℚ) →
    add-located-macneille-ℝ
      ( located-macneille-real-ℚ p)
      ( located-macneille-real-ℚ q) ＝
    located-macneille-real-ℚ (p +ℚ q)
  add-located-macneille-real-ℚ p q =
    eq-type-subtype
      ( is-located-prop-macneille-ℝ)
      ( add-macneille-real-ℚ p q)

  combine-right-add-two-located-macneille-real-ℚ :
    {l : Level} (x : located-macneille-ℝ l) → (p q : ℚ) →
    add-located-macneille-ℝ
      ( add-located-macneille-ℝ x (located-macneille-real-ℚ p))
      ( located-macneille-real-ℚ q) ＝
    add-located-macneille-ℝ x (located-macneille-real-ℚ (p +ℚ q))
  combine-right-add-two-located-macneille-real-ℚ x p q =
    ( associative-add-located-macneille-ℝ
      ( x)
      ( located-macneille-real-ℚ p)
      ( located-macneille-real-ℚ q)) ∙
    ( ap
      ( add-located-macneille-ℝ x)
      ( add-located-macneille-real-ℚ p q))
```

### Interchange laws for addition on located MacNeille real numbers

```agda
module _
  {l1 l2 l3 l4 : Level}
  (x : located-macneille-ℝ l1) (y : located-macneille-ℝ l2)
  (z : located-macneille-ℝ l3) (w : located-macneille-ℝ l4)
  where

  abstract
    interchange-law-add-add-located-macneille-ℝ :
      add-located-macneille-ℝ
        ( add-located-macneille-ℝ x y)
        ( add-located-macneille-ℝ z w) ＝
      add-located-macneille-ℝ
        ( add-located-macneille-ℝ x z)
        ( add-located-macneille-ℝ y w)
    interchange-law-add-add-located-macneille-ℝ =
      equational-reasoning
        add-located-macneille-ℝ
          ( add-located-macneille-ℝ x y)
          ( add-located-macneille-ℝ z w)
        ＝
          add-located-macneille-ℝ
            ( x)
            ( add-located-macneille-ℝ y (add-located-macneille-ℝ z w))
          by associative-add-located-macneille-ℝ _ _ _
        ＝
          add-located-macneille-ℝ
            ( x)
            ( add-located-macneille-ℝ z (add-located-macneille-ℝ y w))
          by
            ap
              ( add-located-macneille-ℝ x)
              ( left-swap-add-located-macneille-ℝ y z w)
        ＝
          add-located-macneille-ℝ
            ( add-located-macneille-ℝ x z)
            ( add-located-macneille-ℝ y w)
          by
            inv
              ( associative-add-located-macneille-ℝ
                ( x)
                ( z)
                ( add-located-macneille-ℝ y w))
```
