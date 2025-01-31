# Addition on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.addition-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.interchange-law
```

</details>

## Idea

We introduce
{{#concept "addition" Disambiguation="rational numbers" Agda=add-ℚ}} on the
[rational numbers](elementary-number-theory.rational-numbers.md) and derive its
basic properties.

## Definition

```agda
add-ℚ : ℚ → ℚ → ℚ
add-ℚ (x , p) (y , q) = rational-fraction-ℤ (add-fraction-ℤ x y)

add-ℚ' : ℚ → ℚ → ℚ
add-ℚ' x y = add-ℚ y x

infixl 35 _+ℚ_
_+ℚ_ = add-ℚ

ap-add-ℚ :
  {x y x' y' : ℚ} → x ＝ x' → y ＝ y' → x +ℚ y ＝ x' +ℚ y'
ap-add-ℚ p q = ap-binary add-ℚ p q
```

## Properties

### Unit laws

```agda
abstract
  left-unit-law-add-ℚ : (x : ℚ) → zero-ℚ +ℚ x ＝ x
  left-unit-law-add-ℚ (x , p) =
    eq-ℚ-sim-fraction-ℤ
      ( add-fraction-ℤ zero-fraction-ℤ x)
      ( x)
      ( left-unit-law-add-fraction-ℤ x) ∙
    is-retraction-rational-fraction-ℚ (x , p)

  right-unit-law-add-ℚ : (x : ℚ) → x +ℚ zero-ℚ ＝ x
  right-unit-law-add-ℚ (x , p) =
    eq-ℚ-sim-fraction-ℤ
      ( add-fraction-ℤ x zero-fraction-ℤ)
      ( x)
      ( right-unit-law-add-fraction-ℤ x) ∙
    is-retraction-rational-fraction-ℚ (x , p)
```

### Addition is associative

```agda
abstract
  associative-add-ℚ :
    (x y z : ℚ) →
    (x +ℚ y) +ℚ z ＝ x +ℚ (y +ℚ z)
  associative-add-ℚ (x , px) (y , py) (z , pz) =
    equational-reasoning
      rational-fraction-ℤ
        (add-fraction-ℤ (pr1 (rational-fraction-ℤ (add-fraction-ℤ x y))) z)
      ＝ rational-fraction-ℤ (add-fraction-ℤ (add-fraction-ℤ x y) z)
        by eq-ℚ-sim-fraction-ℤ _ _
          ( sim-fraction-add-fraction-ℤ
            ( symmetric-sim-fraction-ℤ _ _
              ( sim-reduced-fraction-ℤ (add-fraction-ℤ x y)))
            ( refl-sim-fraction-ℤ z))
      ＝ rational-fraction-ℤ (add-fraction-ℤ x (add-fraction-ℤ y z))
        by eq-ℚ-sim-fraction-ℤ _ _ (associative-add-fraction-ℤ x y z)
      ＝ rational-fraction-ℤ
          ( add-fraction-ℤ x (pr1 (rational-fraction-ℤ (add-fraction-ℤ y z))))
        by eq-ℚ-sim-fraction-ℤ _ _
          ( sim-fraction-add-fraction-ℤ
            ( refl-sim-fraction-ℤ x)
            ( sim-reduced-fraction-ℤ (add-fraction-ℤ y z)))
```

### Addition is commutative

```agda
abstract
  commutative-add-ℚ :
    (x y : ℚ) →
    x +ℚ y ＝ y +ℚ x
  commutative-add-ℚ (x , px) (y , py) =
    eq-ℚ-sim-fraction-ℤ
      ( add-fraction-ℤ x y)
      ( add-fraction-ℤ y x)
      ( commutative-add-fraction-ℤ x y)
```

### Interchange law for addition with respect to addition

```agda
abstract
  interchange-law-add-add-ℚ :
    (x y u v : ℚ) → (x +ℚ y) +ℚ (u +ℚ v) ＝ (x +ℚ u) +ℚ (y +ℚ v)
  interchange-law-add-add-ℚ =
    interchange-law-commutative-and-associative
      add-ℚ
      commutative-add-ℚ
      associative-add-ℚ
```

### The negative of a rational number is its additive inverse

```agda
abstract
  left-inverse-law-add-ℚ : (x : ℚ) → (neg-ℚ x) +ℚ x ＝ zero-ℚ
  left-inverse-law-add-ℚ x =
    ( eq-ℚ-sim-fraction-ℤ
      ( add-fraction-ℤ (neg-fraction-ℤ (fraction-ℚ x)) (fraction-ℚ x))
      ( fraction-ℚ zero-ℚ)
      ( sim-is-zero-numerator-fraction-ℤ
        ( add-fraction-ℤ (neg-fraction-ℤ (fraction-ℚ x)) (fraction-ℚ x))
        ( fraction-ℚ zero-ℚ)
        ( is-zero-numerator-add-left-neg-fraction-ℤ (fraction-ℚ x))
        ( refl))) ∙
    ( is-retraction-rational-fraction-ℚ zero-ℚ)

  right-inverse-law-add-ℚ : (x : ℚ) → x +ℚ (neg-ℚ x) ＝ zero-ℚ
  right-inverse-law-add-ℚ x =
    commutative-add-ℚ x (neg-ℚ x) ∙ left-inverse-law-add-ℚ x
```

### The negatives of rational numbers distribute over addition

```agda
abstract
  distributive-neg-add-ℚ :
    (x y : ℚ) → neg-ℚ (x +ℚ y) ＝ neg-ℚ x +ℚ neg-ℚ y
  distributive-neg-add-ℚ (x , dxp) (y , dyp) =
    ( inv (preserves-neg-rational-fraction-ℤ (x +fraction-ℤ y))) ∙
    ( eq-ℚ-sim-fraction-ℤ
      ( neg-fraction-ℤ (x +fraction-ℤ y))
      ( add-fraction-ℤ (neg-fraction-ℤ x) (neg-fraction-ℤ y))
      ( distributive-neg-add-fraction-ℤ x y))
```

### The inclusion of integer fractions preserves addition

```agda
abstract
  add-rational-fraction-ℤ :
    (x y : fraction-ℤ) →
    rational-fraction-ℤ x +ℚ rational-fraction-ℤ y ＝
    rational-fraction-ℤ (x +fraction-ℤ y)
  add-rational-fraction-ℤ x y =
    eq-ℚ-sim-fraction-ℤ
      ( add-fraction-ℤ (reduce-fraction-ℤ x) (reduce-fraction-ℤ y))
      ( x +fraction-ℤ y)
      ( sim-fraction-add-fraction-ℤ
        ( symmetric-sim-fraction-ℤ
          ( x)
          ( reduce-fraction-ℤ x)
          ( sim-reduced-fraction-ℤ x))
        ( symmetric-sim-fraction-ℤ
          ( y)
          ( reduce-fraction-ℤ y)
          ( sim-reduced-fraction-ℤ y)))
```

## See also

- The additive group structure on the rational numbers is defined in
  [`elementary-number-theory.additive-group-of-rational-numbers`](elementary-number-theory.additive-group-of-rational-numbers.md).
