# Addition on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.addition-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.retractions
open import foundation.sections
```

</details>

## Idea

We introduce
{{#concept "addition" Disambiguation="rational numbers" Agda=add-ℚ}} on the
[rational numbers](elementary-number-theory.rational-numbers.md) and derive its
basic properties.

## Definition

```agda
opaque
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

### The successor and predecessor functions on `ℚ`

```agda
succ-ℚ : ℚ → ℚ
succ-ℚ = add-ℚ one-ℚ

pred-ℚ : ℚ → ℚ
pred-ℚ = add-ℚ neg-one-ℚ
```

## Properties

### Unit laws

```agda
opaque
  unfolding add-ℚ

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
opaque
  unfolding add-ℚ
  unfolding rational-fraction-ℤ

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
opaque
  unfolding add-ℚ

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
opaque
  unfolding add-ℚ neg-ℚ

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

### If `p + q = 0`, then `p = -q`

```agda
abstract
  unique-left-neg-ℚ : (p q : ℚ) → p +ℚ q ＝ zero-ℚ → p ＝ neg-ℚ q
  unique-left-neg-ℚ p q p+q=0 =
    equational-reasoning
      p
      ＝ p +ℚ zero-ℚ by inv (right-unit-law-add-ℚ p)
      ＝ p +ℚ (q +ℚ neg-ℚ q) by ap (p +ℚ_) (inv (right-inverse-law-add-ℚ q))
      ＝ (p +ℚ q) +ℚ neg-ℚ q by inv (associative-add-ℚ _ _ _)
      ＝ zero-ℚ +ℚ neg-ℚ q by ap (_+ℚ neg-ℚ q) p+q=0
      ＝ neg-ℚ q by left-unit-law-add-ℚ _
```

### The negatives of rational numbers distribute over addition

```agda
opaque
  unfolding add-ℚ
  unfolding neg-ℚ

  distributive-neg-add-ℚ :
    (x y : ℚ) → neg-ℚ (x +ℚ y) ＝ neg-ℚ x +ℚ neg-ℚ y
  distributive-neg-add-ℚ (x , dxp) (y , dyp) =
    ( inv (neg-rational-fraction-ℤ (x +fraction-ℤ y))) ∙
    ( eq-ℚ-sim-fraction-ℤ
      ( neg-fraction-ℤ (x +fraction-ℤ y))
      ( add-fraction-ℤ (neg-fraction-ℤ x) (neg-fraction-ℤ y))
      ( distributive-neg-add-fraction-ℤ x y))
```

### The successor and predecessor functions on ℚ are mutual inverses

```agda
opaque
  unfolding add-ℚ
  unfolding neg-ℚ

  is-retraction-pred-ℚ : is-retraction succ-ℚ pred-ℚ
  is-retraction-pred-ℚ x =
    equational-reasoning
      neg-one-ℚ +ℚ (one-ℚ +ℚ x)
      ＝ (neg-one-ℚ +ℚ one-ℚ) +ℚ x
        by inv (associative-add-ℚ neg-one-ℚ one-ℚ x)
      ＝ zero-ℚ +ℚ x
        by ap (_+ℚ x) (left-inverse-law-add-ℚ one-ℚ)
      ＝ x by left-unit-law-add-ℚ x

  is-section-pred-ℚ : is-section succ-ℚ pred-ℚ
  is-section-pred-ℚ x = equational-reasoning
    one-ℚ +ℚ (neg-one-ℚ +ℚ x)
    ＝ (one-ℚ +ℚ neg-one-ℚ) +ℚ x
      by inv (associative-add-ℚ one-ℚ neg-one-ℚ x)
    ＝ zero-ℚ +ℚ x
      by ap (_+ℚ x) (right-inverse-law-add-ℚ one-ℚ)
    ＝ x by left-unit-law-add-ℚ x

  is-equiv-succ-ℚ : is-equiv succ-ℚ
  pr1 (pr1 is-equiv-succ-ℚ) = pred-ℚ
  pr2 (pr1 is-equiv-succ-ℚ) = is-section-pred-ℚ
  pr1 (pr2 is-equiv-succ-ℚ) = pred-ℚ
  pr2 (pr2 is-equiv-succ-ℚ) = is-retraction-pred-ℚ

  is-equiv-pred-ℚ : is-equiv pred-ℚ
  pr1 (pr1 is-equiv-pred-ℚ) = succ-ℚ
  pr2 (pr1 is-equiv-pred-ℚ) = is-retraction-pred-ℚ
  pr1 (pr2 is-equiv-pred-ℚ) = succ-ℚ
  pr2 (pr2 is-equiv-pred-ℚ) = is-section-pred-ℚ

equiv-succ-ℚ : ℚ ≃ ℚ
pr1 equiv-succ-ℚ = succ-ℚ
pr2 equiv-succ-ℚ = is-equiv-succ-ℚ

equiv-pred-ℚ : ℚ ≃ ℚ
pr1 equiv-pred-ℚ = pred-ℚ
pr2 equiv-pred-ℚ = is-equiv-pred-ℚ
```

### The inclusion of integer fractions preserves addition

```agda
opaque
  unfolding add-ℚ
  unfolding rational-fraction-ℤ

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

### The inclusion of integers preserves addition

```agda
abstract
  add-rational-ℤ :
    (x y : ℤ) →
    rational-ℤ x +ℚ rational-ℤ y ＝
    rational-ℤ (x +ℤ y)
  add-rational-ℤ x y = equational-reasoning
    rational-ℤ x +ℚ rational-ℤ y
    ＝ rational-fraction-ℤ (in-fraction-ℤ x) +ℚ
      rational-fraction-ℤ (in-fraction-ℤ y)
      by ap-add-ℚ
        ( inv (is-retraction-rational-fraction-ℚ (rational-ℤ x)))
        ( inv (is-retraction-rational-fraction-ℚ (rational-ℤ y)))
    ＝ rational-fraction-ℤ (in-fraction-ℤ x +fraction-ℤ in-fraction-ℤ y)
      by add-rational-fraction-ℤ (in-fraction-ℤ x) (in-fraction-ℤ y)
    ＝ rational-fraction-ℤ (in-fraction-ℤ (x +ℤ y))
      by eq-ℚ-sim-fraction-ℤ
        ( in-fraction-ℤ x +fraction-ℤ in-fraction-ℤ y)
        ( in-fraction-ℤ (x +ℤ y))
        ( add-in-fraction-ℤ x y)
    ＝ rational-ℤ (x +ℤ y)
      by is-retraction-rational-fraction-ℚ (rational-ℤ (x +ℤ y))
```

### The inclusion of natural numbers preserves addition

```agda
add-rational-ℕ :
  (m n : ℕ) → rational-ℕ m +ℚ rational-ℕ n ＝ rational-ℕ (m +ℕ n)
add-rational-ℕ m n =
  add-rational-ℤ _ _ ∙ ap rational-ℤ (add-int-ℕ m n)
```

### The rational successor of an integer is the successor of the integer

```agda
abstract
  succ-rational-ℤ : (x : ℤ) → succ-ℚ (rational-ℤ x) ＝ rational-ℤ (succ-ℤ x)
  succ-rational-ℤ = add-rational-ℤ one-ℤ
```

### The embedding of the successor of a natural number is the successor of its embedding

```agda
abstract
  succ-rational-ℕ :
    (n : ℕ) → succ-ℚ (rational-ℕ n) ＝ rational-ℕ (succ-ℕ n)
  succ-rational-ℕ n = succ-rational-ℤ _ ∙ ap rational-ℤ (succ-int-ℕ n)
```

## See also

- The additive group structure on the rational numbers is defined in
  [`elementary-number-theory.additive-group-of-rational-numbers`](elementary-number-theory.additive-group-of-rational-numbers.md).
