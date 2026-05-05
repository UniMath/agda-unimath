# Multiplication by positive, negative, and nonnegative rational numbers

```agda
module elementary-number-theory.multiplication-positive-and-negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

When we have information about the sign of the factors of a
[product](elementary-number-theory.multiplication-rational-numbers.md) of
[rational numbers](elementary-number-theory.rational-numbers.md), we can deduce
the sign of their product too.

## Lemmas

### The product of a positive and a negative rational number is negative

```agda
opaque
  unfolding is-positive-ℚ mul-ℚ

  is-negative-mul-positive-negative-ℚ :
    {x y : ℚ} → is-positive-ℚ x → is-negative-ℚ y → is-negative-ℚ (x *ℚ y)
  is-negative-mul-positive-negative-ℚ pos-x neg-y =
    is-negative-rational-fraction-ℤ
      ( is-negative-mul-positive-negative-ℤ
        ( pos-x)
        ( is-negative-fraction-ℚ⁻ (_ , neg-y)))

mul-positive-negative-ℚ : ℚ⁺ → ℚ⁻ → ℚ⁻
mul-positive-negative-ℚ (p , pos-p) (q , neg-q) =
  ( p *ℚ q , is-negative-mul-positive-negative-ℚ pos-p neg-q)
```

### The product of a negative and a positive rational number is negative

```agda
abstract
  is-negative-mul-negative-positive-ℚ :
    {x y : ℚ} → is-negative-ℚ x → is-positive-ℚ y → is-negative-ℚ (x *ℚ y)
  is-negative-mul-negative-positive-ℚ neg-x pos-y =
    tr
      ( is-negative-ℚ)
      ( commutative-mul-ℚ _ _)
      ( is-negative-mul-positive-negative-ℚ pos-y neg-x)

mul-negative-positive-ℚ : ℚ⁻ → ℚ⁺ → ℚ⁻
mul-negative-positive-ℚ (p , neg-p) (q , pos-q) =
  ( p *ℚ q , is-negative-mul-negative-positive-ℚ neg-p pos-q)
```

### The product of a nonnegative and a positive rational number is nonnegative

```agda
opaque
  unfolding is-nonnegative-ℚ is-positive-ℚ mul-ℚ

  is-nonnegative-mul-nonnegative-positive-ℚ :
    {x y : ℚ} → is-nonnegative-ℚ x → is-positive-ℚ y → is-nonnegative-ℚ (x *ℚ y)
  is-nonnegative-mul-nonnegative-positive-ℚ {x} {y} is-nonneg-x is-nonneg-y =
    is-nonnegative-rational-fraction-ℤ
      ( is-nonnegative-mul-nonnegative-positive-ℤ is-nonneg-x is-nonneg-y)
```

### The product of a nonpositive and a positive rational number is nonpositive

```agda
opaque
  unfolding is-nonpositive-ℚ

  is-nonpositive-mul-nonpositive-positive-ℚ :
    {x y : ℚ} → is-nonpositive-ℚ x → is-positive-ℚ y → is-nonpositive-ℚ (x *ℚ y)
  is-nonpositive-mul-nonpositive-positive-ℚ is-nonneg-neg-x is-pos-y =
    tr
      ( is-nonnegative-ℚ)
      ( left-negative-law-mul-ℚ _ _)
      ( is-nonnegative-mul-nonnegative-positive-ℚ is-nonneg-neg-x is-pos-y)

mul-nonpositive-positive-ℚ : ℚ⁰⁻ → ℚ⁺ → ℚ⁰⁻
mul-nonpositive-positive-ℚ (p , is-nonpos-p) (q , is-pos-q) =
  ( p *ℚ q , is-nonpositive-mul-nonpositive-positive-ℚ is-nonpos-p is-pos-q)
```

### The product of a positive and a nonpositive rational number is nonpositive

```agda
abstract
  is-nonpositive-mul-positive-nonpositive-ℚ :
    {x y : ℚ} → is-positive-ℚ x → is-nonpositive-ℚ y → is-nonpositive-ℚ (x *ℚ y)
  is-nonpositive-mul-positive-nonpositive-ℚ is-pos-x is-nonpos-y =
    tr
      ( is-nonpositive-ℚ)
      ( commutative-mul-ℚ _ _)
      ( is-nonpositive-mul-nonpositive-positive-ℚ is-nonpos-y is-pos-x)

mul-positive-nonpositive-ℚ : ℚ⁺ → ℚ⁰⁻ → ℚ⁰⁻
mul-positive-nonpositive-ℚ (p , is-pos-p) (q , is-nonpos-q) =
  ( p *ℚ q , is-nonpositive-mul-positive-nonpositive-ℚ is-pos-p is-nonpos-q)
```

### If `xy` is positive, `x` and `y` are either both negative or both positive

```agda
abstract
  same-sign-is-positive-mul-ℚ :
    {x y : ℚ} → is-positive-ℚ (x *ℚ y) →
    ( ( is-negative-ℚ x × is-negative-ℚ y) +
      ( is-positive-ℚ x × is-positive-ℚ y))
  same-sign-is-positive-mul-ℚ {x} {y} is-pos-xy =
    let
      y≠0 y=0 =
        ex-falso
          ( is-not-positive-zero-ℚ
            ( tr
              ( is-positive-ℚ)
              ( ap-mul-ℚ refl y=0 ∙ right-zero-law-mul-ℚ x)
              ( is-pos-xy)))
    in
      trichotomy-sign-ℚ
        ( x)
        ( λ is-neg-x →
          trichotomy-sign-ℚ
            ( y)
            ( λ is-neg-y → inl (is-neg-x , is-neg-y))
            ( y≠0)
            ( λ is-pos-y →
              ex-falso
                ( is-not-negative-and-positive-ℚ
                  ( is-negative-mul-negative-positive-ℚ is-neg-x is-pos-y ,
                    is-pos-xy))))
        ( λ x=0 →
          ex-falso
            ( is-not-positive-zero-ℚ
              ( tr
                ( is-positive-ℚ)
                ( ap-mul-ℚ x=0 refl ∙ left-zero-law-mul-ℚ y)
                ( is-pos-xy))))
        ( λ is-pos-x →
          trichotomy-sign-ℚ
            ( y)
            ( λ is-neg-y →
              ex-falso
                ( is-not-negative-and-positive-ℚ
                  ( is-negative-mul-positive-negative-ℚ is-pos-x is-neg-y ,
                    is-pos-xy)))
            ( y≠0)
            ( λ is-pos-y → inr (is-pos-x , is-pos-y)))
```

### If `xy` is negative, one of `x` and `y` is positive and the other negative

```agda
abstract
  different-signs-is-negative-mul-ℚ :
    {x y : ℚ} → is-negative-ℚ (x *ℚ y) →
    ( ( is-positive-ℚ x × is-negative-ℚ y) +
      ( is-negative-ℚ x × is-positive-ℚ y))
  different-signs-is-negative-mul-ℚ {x} {y} is-neg-xy =
    map-coproduct
      ( λ (is-neg-neg-x , is-neg-y) →
        ( tr
            ( is-positive-ℚ)
            ( neg-neg-ℚ x)
            ( is-positive-neg-is-negative-ℚ is-neg-neg-x) ,
          is-neg-y))
      ( λ (is-pos-neg-x , is-pos-y) →
        ( tr
            ( is-negative-ℚ)
            ( neg-neg-ℚ x)
            ( is-negative-neg-is-positive-ℚ is-pos-neg-x) ,
          is-pos-y))
      ( same-sign-is-positive-mul-ℚ
        ( inv-tr
          ( is-positive-ℚ)
          ( left-negative-law-mul-ℚ x y)
          ( is-positive-neg-is-negative-ℚ is-neg-xy)))
```
