# The difference between rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.difference-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.integers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
```

</details>

## Idea

The {{#concept "difference" Disambiguation="rational numbers" Agda=diff-ℚ}} of
two [rational numbers](elementary-number-theory.rational-numbers.md) `x` and `y`
is the addition of `x` and the negative of `y`.

## Definitions

```agda
diff-ℚ : ℚ → ℚ → ℚ
diff-ℚ x y = x +ℚ (neg-ℚ y)

infixl 36 _-ℚ_
_-ℚ_ = diff-ℚ

ap-diff-ℚ : {x x' y y' : ℚ} → x ＝ x' → y ＝ y' → x -ℚ y ＝ x' -ℚ y'
ap-diff-ℚ p q = ap-binary diff-ℚ p q
```

## Properties

### Two rational numbers with a difference equal to zero are equal

```agda
abstract
  eq-diff-ℚ : {x y : ℚ} → is-zero-ℚ (x -ℚ y) → x ＝ y
  eq-diff-ℚ {x} {y} H =
    ( inv (right-unit-law-add-ℚ x)) ∙
    ( ap (x +ℚ_) (inv (left-inverse-law-add-ℚ y))) ∙
    ( inv (associative-add-ℚ x (neg-ℚ y) y)) ∙
    ( ap (_+ℚ y) H) ∙
    ( left-unit-law-add-ℚ y)
```

### The difference of a rational number with itself is zero

```agda
abstract
  is-zero-diff-ℚ' : (x : ℚ) → is-zero-ℚ (x -ℚ x)
  is-zero-diff-ℚ' = right-inverse-law-add-ℚ
```

### The difference of two equal rational numbers is zero

```agda
abstract
  is-zero-diff-ℚ : {x y : ℚ} → x ＝ y → is-zero-ℚ (x -ℚ y)
  is-zero-diff-ℚ {x} refl = is-zero-diff-ℚ' x
```

### The difference of a rational number with zero is itself

```agda
opaque
  unfolding neg-ℚ

  right-zero-law-diff-ℚ : (x : ℚ) → x -ℚ zero-ℚ ＝ x
  right-zero-law-diff-ℚ = right-unit-law-add-ℚ
```

### The difference of zero and a rational number is its negative

```agda
abstract
  left-zero-law-diff-ℚ : (x : ℚ) → zero-ℚ -ℚ x ＝ neg-ℚ x
  left-zero-law-diff-ℚ x = left-unit-law-add-ℚ (neg-ℚ x)
```

### If the difference of two rational numbers is zero, they are equal

```agda
abstract
  eq-is-zero-diff-ℚ : (x y : ℚ) → x -ℚ y ＝ zero-ℚ → x ＝ y
  eq-is-zero-diff-ℚ x y x-y=0 =
    inv
      ( equational-reasoning
        y
        ＝ zero-ℚ +ℚ y by inv (left-unit-law-add-ℚ y)
        ＝ (x -ℚ y) +ℚ y by ap (_+ℚ y) (inv x-y=0)
        ＝ x +ℚ (neg-ℚ y +ℚ y) by associative-add-ℚ _ _ _
        ＝ x +ℚ zero-ℚ by ap (x +ℚ_) (left-inverse-law-add-ℚ y)
        ＝ x by right-unit-law-add-ℚ x)
```

### Triangular identity for addition and difference of rational numbers

```agda
abstract
  triangle-diff-ℚ :
    (x y z : ℚ) → (x -ℚ y) +ℚ (y -ℚ z) ＝ x -ℚ z
  triangle-diff-ℚ x y z =
    ( associative-add-ℚ x (neg-ℚ y) (y -ℚ z)) ∙
    ( ap
      ( x +ℚ_)
      { neg-ℚ y +ℚ y -ℚ z}
      { neg-ℚ z}
      ( ( inv (associative-add-ℚ (neg-ℚ y) y (neg-ℚ z))) ∙
        ( ( ap
            (_+ℚ (neg-ℚ z))
            { neg-ℚ y +ℚ y}
            { zero-ℚ}
            ( left-inverse-law-add-ℚ y)) ∙
          ( left-unit-law-add-ℚ (neg-ℚ z)))))
```

### The negative of the difference of two rational numbers `x` and `y` is the difference of `y` and `x`

```agda
abstract
  distributive-neg-diff-ℚ :
    (x y : ℚ) → neg-ℚ (x -ℚ y) ＝ y -ℚ x
  distributive-neg-diff-ℚ x y =
    ( distributive-neg-add-ℚ x (neg-ℚ y)) ∙
    ( ap ((neg-ℚ x) +ℚ_) (neg-neg-ℚ y)) ∙
    ( commutative-add-ℚ (neg-ℚ x) y)
```

### Interchange laws for addition and difference on rational numbers

```agda
abstract
  interchange-law-diff-add-ℚ :
    (x y u v : ℚ) → (x +ℚ y) -ℚ (u +ℚ v) ＝ (x -ℚ u) +ℚ (y -ℚ v)
  interchange-law-diff-add-ℚ x y u v =
    ( ap ((x +ℚ y) +ℚ_) (distributive-neg-add-ℚ u v)) ∙
    ( interchange-law-add-add-ℚ x y (neg-ℚ u) (neg-ℚ v))

  interchange-law-add-diff-ℚ :
    (x y u v : ℚ) → (x -ℚ y) +ℚ (u -ℚ v) ＝ (x +ℚ u) -ℚ (y +ℚ v)
  interchange-law-add-diff-ℚ x y u v =
    inv (interchange-law-diff-add-ℚ x u y v)
```

### The difference of rational numbers is invariant by translation

```agda
abstract
  left-translation-diff-ℚ :
    (x y z : ℚ) → (z +ℚ x) -ℚ (z +ℚ y) ＝ x -ℚ y
  left-translation-diff-ℚ x y z =
    ( interchange-law-diff-add-ℚ z x z y) ∙
    ( ap (_+ℚ (x -ℚ y)) (right-inverse-law-add-ℚ z)) ∙
    ( left-unit-law-add-ℚ (x -ℚ y))

  right-translation-diff-ℚ :
    (x y z : ℚ) → (x +ℚ z) -ℚ (y +ℚ z) ＝ x -ℚ y
  right-translation-diff-ℚ x y z =
    ( ap-diff-ℚ (commutative-add-ℚ x z) (commutative-add-ℚ y z)) ∙
    ( left-translation-diff-ℚ x y z)
```

### The inclusion of integers preserves differences

```agda
abstract
  diff-rational-ℤ :
    (x y : ℤ) → rational-ℤ x -ℚ rational-ℤ y ＝ rational-ℤ (x -ℤ y)
  diff-rational-ℤ x y =
    equational-reasoning
      rational-ℤ x -ℚ rational-ℤ y
      ＝ rational-ℤ x +ℚ rational-ℤ (neg-ℤ y)
        by ap (rational-ℤ x +ℚ_) (inv (neg-rational-ℤ y))
      ＝ rational-ℤ (x -ℤ y)
        by add-rational-ℤ x (neg-ℤ y)
```

### The difference of the successor of a rational number and the rational number is one

```agda
abstract
  diff-succ-ℚ : (q : ℚ) → succ-ℚ q -ℚ q ＝ one-ℚ
  diff-succ-ℚ q =
    equational-reasoning
      (one-ℚ +ℚ q) -ℚ q
      ＝ one-ℚ +ℚ (q -ℚ q)
        by associative-add-ℚ _ _ _
      ＝ one-ℚ +ℚ zero-ℚ
        by ap-add-ℚ refl (right-inverse-law-add-ℚ q)
      ＝ one-ℚ
        by right-unit-law-add-ℚ _
```
