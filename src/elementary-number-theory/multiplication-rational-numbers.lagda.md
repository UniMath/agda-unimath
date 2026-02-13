# Multiplication on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.interchange-law

open import group-theory.multiples-of-elements-abelian-groups
```

</details>

## Idea

{{#concept "Multiplication" WDID=Q40276 WD="multiplication" Disambiguation="of rational numbers" Agda=mul-ℚ}}
on the [rational numbers](elementary-number-theory.rational-numbers.md) is
defined by extending
[multiplication](elementary-number-theory.multiplication-integer-fractions.md)
on [integer fractions](elementary-number-theory.integer-fractions.md) to the
rational numbers.

## Definition

```agda
opaque
  mul-ℚ : ℚ → ℚ → ℚ
  mul-ℚ (x , p) (y , q) = rational-fraction-ℤ (mul-fraction-ℤ x y)

mul-ℚ' : ℚ → ℚ → ℚ
mul-ℚ' x y = mul-ℚ y x

infixl 40 _*ℚ_
_*ℚ_ = mul-ℚ

ap-mul-ℚ :
  {x y x' y' : ℚ} → x ＝ x' → y ＝ y' → x *ℚ y ＝ x' *ℚ y'
ap-mul-ℚ p q = ap-binary mul-ℚ p q
```

## Properties

### The multiplication of a rational number by zero is zero

```agda
module _
  (x : ℚ)
  where

  opaque
    unfolding mul-ℚ

    left-zero-law-mul-ℚ : zero-ℚ *ℚ x ＝ zero-ℚ
    left-zero-law-mul-ℚ =
      ( eq-ℚ-sim-fraction-ℤ
        ( mul-fraction-ℤ (fraction-ℚ zero-ℚ) (fraction-ℚ x))
        ( fraction-ℚ zero-ℚ)
        ( eq-is-zero-ℤ
          ( ap (mul-ℤ' one-ℤ) (left-zero-law-mul-ℤ (numerator-ℚ x)))
          ( left-zero-law-mul-ℤ _))) ∙
      ( is-retraction-rational-fraction-ℚ zero-ℚ)

    right-zero-law-mul-ℚ : x *ℚ zero-ℚ ＝ zero-ℚ
    right-zero-law-mul-ℚ =
      ( eq-ℚ-sim-fraction-ℤ
        ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ zero-ℚ))
        ( fraction-ℚ zero-ℚ)
        ( eq-is-zero-ℤ
          ( ap (mul-ℤ' one-ℤ) (right-zero-law-mul-ℤ (numerator-ℚ x)))
          ( left-zero-law-mul-ℤ _))) ∙
      ( is-retraction-rational-fraction-ℚ zero-ℚ)
```

### If the product of two rational numbers is zero, the left or right factor is zero

```agda
opaque
  unfolding mul-ℚ
  unfolding rational-fraction-ℤ

  decide-is-zero-factor-is-zero-mul-ℚ :
    (x y : ℚ) → is-zero-ℚ (x *ℚ y) → (is-zero-ℚ x) + (is-zero-ℚ y)
  decide-is-zero-factor-is-zero-mul-ℚ x y H =
    rec-coproduct
      ( inl ∘ is-zero-is-zero-numerator-ℚ x)
      ( inr ∘ is-zero-is-zero-numerator-ℚ y)
      ( is-zero-is-zero-mul-ℤ
        ( numerator-ℚ x)
        ( numerator-ℚ y)
        ( ( inv
            ( eq-reduce-numerator-fraction-ℤ
              ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))) ∙
          ( ap
            ( mul-ℤ'
              ( gcd-ℤ
                ( numerator-ℚ x *ℤ numerator-ℚ y)
                ( denominator-ℚ x *ℤ denominator-ℚ y)))
            ( ( is-zero-numerator-is-zero-ℚ (x *ℚ y) H) ∙
              ( left-zero-law-mul-ℤ
                ( gcd-ℤ
                  (numerator-ℚ x *ℤ numerator-ℚ y)
                  (denominator-ℚ x *ℤ denominator-ℚ y)))))))
```

### Unit laws for multiplication on rational numbers

```agda
opaque
  unfolding mul-ℚ

  left-unit-law-mul-ℚ : (x : ℚ) → one-ℚ *ℚ x ＝ x
  left-unit-law-mul-ℚ x =
    ( eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ one-fraction-ℤ (fraction-ℚ x))
      ( fraction-ℚ x)
      ( left-unit-law-mul-fraction-ℤ (fraction-ℚ x))) ∙
    ( is-retraction-rational-fraction-ℚ x)

  right-unit-law-mul-ℚ : (x : ℚ) → x *ℚ one-ℚ ＝ x
  right-unit-law-mul-ℚ x =
    ( eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ x) one-fraction-ℤ)
      ( fraction-ℚ x)
      ( right-unit-law-mul-fraction-ℤ (fraction-ℚ x))) ∙
    ( is-retraction-rational-fraction-ℚ x)
```

### Multiplication of a rational number by `-1` is equal to the negative

```agda
opaque
  unfolding mul-ℚ
  unfolding neg-ℚ

  left-neg-unit-law-mul-ℚ : (x : ℚ) → neg-one-ℚ *ℚ x ＝ neg-ℚ x
  left-neg-unit-law-mul-ℚ x =
    ( eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ neg-one-ℚ) (fraction-ℚ x))
      ( neg-fraction-ℤ (fraction-ℚ x))
      ( ap-mul-ℤ
        ( left-neg-unit-law-mul-ℤ (numerator-ℚ x))
        ( inv (left-unit-law-mul-ℤ (denominator-ℚ x))))) ∙
    ( is-retraction-rational-fraction-ℚ (neg-ℚ x))

  right-neg-unit-law-mul-ℚ : (x : ℚ) → x *ℚ neg-one-ℚ ＝ neg-ℚ x
  right-neg-unit-law-mul-ℚ x =
    ( eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ neg-one-ℚ))
      ( neg-fraction-ℤ (fraction-ℚ x))
      ( ap-mul-ℤ
        ( right-neg-unit-law-mul-ℤ (numerator-ℚ x))
        ( inv (right-unit-law-mul-ℤ (denominator-ℚ x))))) ∙
    ( is-retraction-rational-fraction-ℚ (neg-ℚ x))
```

### Multiplication of rational numbers is associative

```agda
opaque
  unfolding mul-ℚ
  unfolding rational-fraction-ℤ

  associative-mul-ℚ :
    (x y z : ℚ) → (x *ℚ y) *ℚ z ＝ x *ℚ (y *ℚ z)
  associative-mul-ℚ x y z =
    eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ z))
      ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y *ℚ z)))
      ( transitive-sim-fraction-ℤ
        ( mul-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ z))
        ( mul-fraction-ℤ
          ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
          ( fraction-ℚ z))
        ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y *ℚ z)))
        ( transitive-sim-fraction-ℤ
          ( mul-fraction-ℤ
            ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
            ( fraction-ℚ z))
          ( mul-fraction-ℤ
            ( fraction-ℚ x)
            ( mul-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
          ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y *ℚ z)))
          ( sim-fraction-mul-fraction-ℤ
            ( refl-sim-fraction-ℤ (fraction-ℚ x))
            ( sim-reduced-fraction-ℤ
              ( mul-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z))))
          ( associative-mul-fraction-ℤ
            ( fraction-ℚ x)
            ( fraction-ℚ y)
            ( fraction-ℚ z)))
        ( sim-fraction-mul-fraction-ℤ
          ( inv
            ( sim-reduced-fraction-ℤ
              ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
          ( refl-sim-fraction-ℤ (fraction-ℚ z))))
```

### Multiplication of rational numbers is commutative

```agda
opaque
  unfolding mul-ℚ

  commutative-mul-ℚ : (x y : ℚ) → x *ℚ y ＝ y *ℚ x
  commutative-mul-ℚ x y =
    eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
      ( mul-fraction-ℤ (fraction-ℚ y) (fraction-ℚ x))
      ( commutative-mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
```

### Interchange law for multiplication on rational numbers with itself

```agda
abstract
  interchange-law-mul-mul-ℚ :
    (x y u v : ℚ) → (x *ℚ y) *ℚ (u *ℚ v) ＝ (x *ℚ u) *ℚ (y *ℚ v)
  interchange-law-mul-mul-ℚ =
    interchange-law-commutative-and-associative
      mul-ℚ
      commutative-mul-ℚ
      associative-mul-ℚ
```

### Swapping laws for multiplication

```agda
abstract
  left-swap-mul-ℚ : (x y z : ℚ) → x *ℚ (y *ℚ z) ＝ y *ℚ (x *ℚ z)
  left-swap-mul-ℚ x y z =
    equational-reasoning
      x *ℚ (y *ℚ z)
      ＝ (x *ℚ y) *ℚ z by inv (associative-mul-ℚ x y z)
      ＝ (y *ℚ x) *ℚ z by ap-mul-ℚ (commutative-mul-ℚ x y) refl
      ＝ y *ℚ (x *ℚ z) by associative-mul-ℚ y x z
```

### Negative laws for multiplication on rational numbers

```agda
module _
  (x y : ℚ)
  where

  abstract
    left-negative-law-mul-ℚ : (neg-ℚ x) *ℚ y ＝ neg-ℚ (x *ℚ y)
    left-negative-law-mul-ℚ =
      ( ap ( _*ℚ y) (inv (left-neg-unit-law-mul-ℚ x))) ∙
      ( associative-mul-ℚ neg-one-ℚ x y) ∙
      ( left-neg-unit-law-mul-ℚ (x *ℚ y))

    right-negative-law-mul-ℚ : x *ℚ (neg-ℚ y) ＝ neg-ℚ (x *ℚ y)
    right-negative-law-mul-ℚ =
      ( ap ( x *ℚ_) (inv (right-neg-unit-law-mul-ℚ y))) ∙
      ( inv (associative-mul-ℚ x y neg-one-ℚ)) ∙
      ( right-neg-unit-law-mul-ℚ (x *ℚ y))

abstract
  negative-law-mul-ℚ : (x y : ℚ) → (neg-ℚ x) *ℚ (neg-ℚ y) ＝ x *ℚ y
  negative-law-mul-ℚ x y =
    ( left-negative-law-mul-ℚ x (neg-ℚ y)) ∙
    ( ap neg-ℚ (right-negative-law-mul-ℚ x y)) ∙
    ( neg-neg-ℚ (x *ℚ y))

  swap-neg-mul-ℚ : (x y : ℚ) → x *ℚ (neg-ℚ y) ＝ (neg-ℚ x) *ℚ y
  swap-neg-mul-ℚ x y =
    ( right-negative-law-mul-ℚ x y) ∙
    ( inv (left-negative-law-mul-ℚ x y))
```

### Multiplication on rational numbers distributes over addition

```agda
opaque
  unfolding add-ℚ
  unfolding mul-ℚ
  unfolding rational-fraction-ℤ

  left-distributive-mul-add-ℚ :
    (x y z : ℚ) → x *ℚ (y +ℚ z) ＝ (x *ℚ y) +ℚ (x *ℚ z)
  left-distributive-mul-add-ℚ x y z =
    eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y +ℚ z)))
      ( add-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ (x *ℚ z)))
      ( transitive-sim-fraction-ℤ
        ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y +ℚ z)))
        ( mul-fraction-ℤ
          ( fraction-ℚ x)
          ( add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
        ( add-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ (x *ℚ z)))
        ( transitive-sim-fraction-ℤ
          ( mul-fraction-ℤ
            ( fraction-ℚ x)
            ( add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
          ( add-fraction-ℤ
            ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
            ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ z)))
          ( add-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ (x *ℚ z)))
          ( sim-fraction-add-fraction-ℤ
            ( sim-reduced-fraction-ℤ
              ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
            ( sim-reduced-fraction-ℤ
              ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ z))))
          ( left-distributive-mul-add-fraction-ℤ
            ( fraction-ℚ x)
            ( fraction-ℚ y)
            ( fraction-ℚ z)))
        ( sim-fraction-mul-fraction-ℤ
          ( refl-sim-fraction-ℤ (fraction-ℚ x))
          ( transitive-sim-fraction-ℤ
            ( fraction-ℚ (y +ℚ z))
            ( reduce-fraction-ℤ (add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
            ( add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z))
            ( symmetric-sim-fraction-ℤ
              ( add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z))
              ( reduce-fraction-ℤ
                ( add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
              ( sim-reduced-fraction-ℤ
                (add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z))))
            ( refl-sim-fraction-ℤ (fraction-ℚ (y +ℚ z))))))

  right-distributive-mul-add-ℚ :
    (x y z : ℚ) → (x +ℚ y) *ℚ z ＝ (x *ℚ z) +ℚ (y *ℚ z)
  right-distributive-mul-add-ℚ x y z =
    ( commutative-mul-ℚ (x +ℚ y) z) ∙
    ( left-distributive-mul-add-ℚ z x y) ∙
    ( ap-add-ℚ (commutative-mul-ℚ z x) (commutative-mul-ℚ z y))
```

### Multiplication on rational numbers distributes over the difference

```agda
abstract
  left-distributive-mul-diff-ℚ :
    (z x y : ℚ) → z *ℚ (x -ℚ y) ＝ (z *ℚ x) -ℚ (z *ℚ y)
  left-distributive-mul-diff-ℚ z x y =
    ( left-distributive-mul-add-ℚ z x (neg-ℚ y)) ∙
    ( ap ((z *ℚ x) +ℚ_) (right-negative-law-mul-ℚ z y))

  right-distributive-mul-diff-ℚ :
    (x y z : ℚ) → (x -ℚ y) *ℚ z ＝ (x *ℚ z) -ℚ (y *ℚ z)
  right-distributive-mul-diff-ℚ x y z =
    ( right-distributive-mul-add-ℚ x (neg-ℚ y) z) ∙
    ( ap ((x *ℚ z) +ℚ_) (left-negative-law-mul-ℚ y z))
```

### The inclusion of integer fractions preserves multiplication

```agda
opaque
  unfolding mul-ℚ
  unfolding rational-fraction-ℤ

  mul-rational-fraction-ℤ :
    (x y : fraction-ℤ) →
    rational-fraction-ℤ x *ℚ rational-fraction-ℤ y ＝
    rational-fraction-ℤ (x *fraction-ℤ y)
  mul-rational-fraction-ℤ x y =
    eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ (reduce-fraction-ℤ x) (reduce-fraction-ℤ y))
      ( x *fraction-ℤ y)
      ( sim-fraction-mul-fraction-ℤ
        ( symmetric-sim-fraction-ℤ
          ( x)
          ( reduce-fraction-ℤ x)
          ( sim-reduced-fraction-ℤ x))
        ( symmetric-sim-fraction-ℤ
          ( y)
          ( reduce-fraction-ℤ y)
          ( sim-reduced-fraction-ℤ y)))
```

### The inclusion of integers preserves multiplication

```agda
abstract
  mul-rational-ℤ :
    (x y : ℤ) → rational-ℤ x *ℚ rational-ℤ y ＝ rational-ℤ (x *ℤ y)
  mul-rational-ℤ x y =
    equational-reasoning
      rational-ℤ x *ℚ rational-ℤ y
      ＝
        rational-fraction-ℤ (in-fraction-ℤ x) *ℚ
        rational-fraction-ℤ (in-fraction-ℤ y)
        by
          ap-mul-ℚ
            ( inv (is-retraction-rational-fraction-ℚ (rational-ℤ x)))
            ( inv (is-retraction-rational-fraction-ℚ (rational-ℤ y)))
      ＝
        rational-fraction-ℤ (in-fraction-ℤ x *fraction-ℤ in-fraction-ℤ y)
        by mul-rational-fraction-ℤ _ _
      ＝ rational-fraction-ℤ (in-fraction-ℤ (x *ℤ y))
        by ap rational-fraction-ℤ (mul-in-fraction-ℤ x y)
      ＝ rational-ℤ (x *ℤ y) by is-retraction-rational-fraction-ℚ _
```

### The inclusion of natural numbers preserves multiplication

```agda
abstract
  mul-rational-ℕ :
    (x y : ℕ) → rational-ℕ x *ℚ rational-ℕ y ＝ rational-ℕ (x *ℕ y)
  mul-rational-ℕ x y = mul-rational-ℤ _ _ ∙ ap rational-ℤ (mul-int-ℕ x y)
```

### `succ-ℚ p * q = q + (p * q)`

```agda
abstract
  mul-left-succ-ℚ :
    (p q : ℚ) →
    (succ-ℚ p *ℚ q) ＝ q +ℚ (p *ℚ q)
  mul-left-succ-ℚ p q =
    equational-reasoning
      succ-ℚ p *ℚ q
      ＝ (one-ℚ *ℚ q) +ℚ (p *ℚ q)
        by right-distributive-mul-add-ℚ one-ℚ p q
      ＝ q +ℚ (p *ℚ q) by ap-add-ℚ (left-unit-law-mul-ℚ q) refl

  mul-right-succ-ℚ :
    (p q : ℚ) →
    (p *ℚ succ-ℚ q) ＝ p +ℚ (p *ℚ q)
  mul-right-succ-ℚ p q =
    equational-reasoning
      p *ℚ succ-ℚ q
      ＝ (p *ℚ one-ℚ) +ℚ (p *ℚ q)
        by left-distributive-mul-add-ℚ p one-ℚ q
      ＝ p +ℚ (p *ℚ q)
        by ap-add-ℚ (right-unit-law-mul-ℚ p) refl
```

### Multiplication by a natural number is repeated addition

```agda
abstract
  left-mul-rational-nat-ℚ :
    (n : ℕ) (q : ℚ) → rational-ℕ n *ℚ q ＝ multiple-Ab abelian-group-add-ℚ n q
  left-mul-rational-nat-ℚ 0 q = left-zero-law-mul-ℚ q
  left-mul-rational-nat-ℚ 1 q = left-unit-law-mul-ℚ q
  left-mul-rational-nat-ℚ (succ-ℕ n@(succ-ℕ _)) q =
    equational-reasoning
      rational-ℕ (succ-ℕ n) *ℚ q
      ＝ succ-ℚ (rational-ℕ n) *ℚ q
        by ap-mul-ℚ (inv (succ-rational-ℕ n)) refl
      ＝ q +ℚ rational-ℕ n *ℚ q by
        mul-left-succ-ℚ _ _
      ＝ q +ℚ multiple-Ab abelian-group-add-ℚ n q
        by ap-add-ℚ refl (left-mul-rational-nat-ℚ n q)
      ＝ multiple-Ab abelian-group-add-ℚ (succ-ℕ n) q
        by inv (multiple-succ-Ab' abelian-group-add-ℚ n q)

  eq-succ-mul-rational-ℕ-right-ℚ :
    (n : ℕ) (q : ℚ) →
    q +ℚ (rational-ℕ n *ℚ q) ＝ rational-ℕ (succ-ℕ n) *ℚ q
  eq-succ-mul-rational-ℕ-right-ℚ n q =
    inv
      ( ( ap-mul-ℚ (inv (succ-rational-ℕ n)) refl) ∙
        ( mul-left-succ-ℚ (rational-ℕ n) q))
```

### `2q = q + q`

```agda
abstract
  mul-two-ℚ : (q : ℚ) → rational-ℕ 2 *ℚ q ＝ q +ℚ q
  mul-two-ℚ = left-mul-rational-nat-ℚ 2

  twice-one-ℚ : one-ℚ +ℚ one-ℚ ＝ rational-ℕ 2
  twice-one-ℚ =
    inv (mul-two-ℚ one-ℚ) ∙
    right-unit-law-mul-ℚ (rational-ℕ 2)
```

### The product of a rational number and its denominator is its numerator

```agda
module _
  (x : ℚ)
  where

  opaque
    unfolding mul-ℚ

    eq-numerator-mul-denominator-ℚ :
      mul-ℚ
        ( x)
        ( rational-ℤ (denominator-ℚ x)) ＝
      rational-ℤ (numerator-ℚ x)
    eq-numerator-mul-denominator-ℚ =
      ( eq-ℚ-sim-fraction-ℤ
        ( mul-fraction-ℤ
          ( fraction-ℚ x)
          ( in-fraction-ℤ (denominator-ℚ x)))
        ( in-fraction-ℤ (numerator-ℚ x))
        ( associative-mul-ℤ
          ( numerator-ℚ x)
          ( denominator-ℚ x)
          ( one-ℤ))) ∙
      ( is-retraction-rational-fraction-ℚ
        ( rational-ℤ (numerator-ℚ x)))

    eq-numerator-mul-denominator-ℚ' :
      mul-ℚ
        ( rational-ℤ (denominator-ℚ x))
        ( x) ＝
      rational-ℤ (numerator-ℚ x)
    eq-numerator-mul-denominator-ℚ' =
      ( commutative-mul-ℚ
        ( rational-ℤ (denominator-ℚ x))
        ( x)) ∙
      ( eq-numerator-mul-denominator-ℚ)
```

## See also

- The multiplicative monoid structure on the rational numbers is defined in
  [`elementary-number-theory.multiplicative-monoid-of-rational-numbers`](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md);
- The multiplicative group structure on the rational numbers is defined in
  [`elementary-number-theory.multiplicative-group-of-rational-numbers`](elementary-number-theory.multiplicative-group-of-rational-numbers.md).
