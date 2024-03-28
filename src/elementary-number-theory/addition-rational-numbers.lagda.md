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
open import foundation.dependent-pair-types
open import foundation.identity-types
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
left-unit-law-add-ℚ : (x : ℚ) → zero-ℚ +ℚ x ＝ x
left-unit-law-add-ℚ (x , p) =
  eq-ℚ-sim-fraction-ℤ
    ( add-fraction-ℤ zero-fraction-ℤ x)
    ( x)
    ( left-unit-law-add-fraction-ℤ x) ∙
  rational-fraction-fraction-ℚ (x , p)

right-unit-law-add-ℚ : (x : ℚ) → x +ℚ zero-ℚ ＝ x
right-unit-law-add-ℚ (x , p) =
  eq-ℚ-sim-fraction-ℤ
    ( add-fraction-ℤ x zero-fraction-ℤ)
    ( x)
    ( right-unit-law-add-fraction-ℤ x) ∙
  rational-fraction-fraction-ℚ (x , p)
```

### Addition is associative

```agda
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
commutative-add-ℚ :
  (x y : ℚ) →
  x +ℚ y ＝ y +ℚ x
commutative-add-ℚ (x , px) (y , py) =
  eq-ℚ-sim-fraction-ℤ
    ( add-fraction-ℤ x y)
    ( add-fraction-ℤ y x)
    ( commutative-add-fraction-ℤ x y)
```

### The negative of a rational number is its additive inverse

```agda
left-inverse-law-add-ℚ : (x : ℚ) → (neg-ℚ x) +ℚ x ＝ zero-ℚ
left-inverse-law-add-ℚ x =
  eq-ℚ-sim-fraction-ℤ
    ( add-fraction-ℤ (neg-fraction-ℤ (fraction-ℚ x)) (fraction-ℚ x))
    ( fraction-ℚ zero-ℚ)
    ( sim-is-zero-numerator-fraction-ℤ
      ( add-fraction-ℤ (neg-fraction-ℤ (fraction-ℚ x)) (fraction-ℚ x))
      ( fraction-ℚ zero-ℚ)
      ( is-zero-numerator-add-left-neg-fraction-ℤ (fraction-ℚ x))
      ( refl)) ∙
  rational-fraction-fraction-ℚ zero-ℚ

right-inverse-law-add-ℚ : (x : ℚ) → x +ℚ (neg-ℚ x) ＝ zero-ℚ
right-inverse-law-add-ℚ x =
  commutative-add-ℚ x (neg-ℚ x) ∙ left-inverse-law-add-ℚ x
```

## See also

- The additive group structure on the rational numbers is defined in
  [elementary-number-theory.group-of-rational-numbers.md].
