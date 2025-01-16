# Farey fractions

```agda
module elementary-number-theory.farey-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "Farey fraction" Agda=farey-fraction}} is a [reduced](elementary-number-theory.reduced-integer-fractions.md) [integer fraction](elementary-number-theory.integer-fractions.md) between $0$ and $1$ inclusive. More specifically, a Farey fraction of order $n$ is a reduced integer fraction between $0$ and $1$ whose denominator does not exceed $n$.

The Farey fractions ℱ can be inductively generated mutually with a binary relation $R$ with the following constructors:

```text
  0 : ℱ
  1 : ℱ
  𝓂 : (x y : ℱ) → ℛ x y → ℱ

  𝓈 : ℛ 0 1
  𝓇 : (x y : ℱ) (r : ℛ x y) → ℛ x (𝓂 x y r)
  𝓁 : (x y : ℱ) (r : ℛ x y) → ℛ (𝓂 x y r) y
```

The operation $m$ returns the {{#concept "mediant" Disambiguation="Farey fractions"}} of two adjacent Farey fractions. The elements $0$ and $1$ in the type of Farey fractions represent the Farey fractions $0/1$ and $1/1$. Given two adjacent Farey fractions representing $a/b$ and $c/d$, the mediant of $a/b$ and $c/d$ is the Farey fraction representing

$$
  \frac{a+c}{b+d}.
$$

The mediant of any two adjacent Farey fractions representing reduced fractions $a/b$ and $c/d$ represents again a reduced fraction. 

Farey fractions appear in Chapter 3 of {{#cite HW08}}, but they are covered in more detail in Chapter 6 of {{#cite NZM}}. 

## Definitions

### The inductively generated Farey fractions

```agda
mutual

  data
    farey-fraction : UU lzero
    where

    zero-farey-fraction : farey-fraction
    one-farey-fraction : farey-fraction

    mediant-farey-fraction :
      (x y : farey-fraction) → adjacent-farey-fraction x y → farey-fraction

  data
    adjacent-farey-fraction : farey-fraction → farey-fraction → UU lzero
    where

    adjacent-zero-one-farey-fraction :
      adjacent-farey-fraction zero-farey-fraction one-farey-fraction

    right-adjacent-mediant-farey-fraction :
      (x y : farey-fraction) (H : adjacent-farey-fraction x y) →
      adjacent-farey-fraction x (mediant-farey-fraction x y H)

    left-adjacent-mediant-farey-fraction :
      (x y : farey-fraction) (H : adjacent-farey-fraction x y) →
      adjacent-farey-fraction (mediant-farey-fraction x y H) y
```

### The inclusion of Farey fractions into the integer fractions

```agda
numerator-farey-fraction :
  farey-fraction → ℕ
numerator-farey-fraction zero-farey-fraction =
  0
numerator-farey-fraction one-farey-fraction =
  1
numerator-farey-fraction (mediant-farey-fraction x y H) =
  numerator-farey-fraction x +ℕ numerator-farey-fraction y

denominator-farey-fraction :
  farey-fraction → ℕ
denominator-farey-fraction zero-farey-fraction =
  1
denominator-farey-fraction one-farey-fraction =
  1
denominator-farey-fraction (mediant-farey-fraction x y H) =
  denominator-farey-fraction x +ℕ denominator-farey-fraction y
```

## Properties

### Any two adjacent Farey fractions $a/b$ and $c/d$ satisfy $bc = ad + 1$

Equivalently, two adjacent Farey fractions $a/b$ and $c/d$ satisfy the relation

$$
  bc - ad = 1.
$$

This is also known as the **characteristic property of adjacent Farey fractions**.

```agda
characteristic-property-adjacent-farey-fraction :
  (x y : farey-fraction) (r : adjacent-farey-fraction x y) →
  denominator-farey-fraction x *ℕ numerator-farey-fraction y ＝
  numerator-farey-fraction x *ℕ denominator-farey-fraction y +ℕ 1
characteristic-property-adjacent-farey-fraction ._ ._
  adjacent-zero-one-farey-fraction =
  refl
characteristic-property-adjacent-farey-fraction x ._
  ( right-adjacent-mediant-farey-fraction .x y r) =
  left-distributive-mul-add-ℕ
    ( denominator-farey-fraction x)
    ( numerator-farey-fraction x)
    ( numerator-farey-fraction y) ∙
  ap-add-ℕ
    ( commutative-mul-ℕ
      ( denominator-farey-fraction x)
      ( numerator-farey-fraction x))
    ( characteristic-property-adjacent-farey-fraction x y r) ∙
  ap
    ( succ-ℕ)
    ( inv
      ( left-distributive-mul-add-ℕ
        ( numerator-farey-fraction x)
        ( denominator-farey-fraction x)
        ( denominator-farey-fraction y)))
characteristic-property-adjacent-farey-fraction ._ y
  ( left-adjacent-mediant-farey-fraction x .y r) =
  right-distributive-mul-add-ℕ
    ( denominator-farey-fraction x)
    ( denominator-farey-fraction y)
    ( numerator-farey-fraction y) ∙
  ap-add-ℕ
    ( characteristic-property-adjacent-farey-fraction x y r)
    ( commutative-mul-ℕ
      ( denominator-farey-fraction y)
      ( numerator-farey-fraction y)) ∙
  left-successor-law-add-ℕ
    ( numerator-farey-fraction x *ℕ denominator-farey-fraction y)
    ( numerator-farey-fraction y *ℕ denominator-farey-fraction y) ∙
  ap
    ( succ-ℕ)
    ( inv
      ( right-distributive-mul-add-ℕ
        ( numerator-farey-fraction x)
        ( numerator-farey-fraction y)
        ( denominator-farey-fraction y)))
```

## See also

- [Unbounded Farey fractions](elementary-number-theory.unbounded-farey-fractions.md)

## References

{{#bibliography}}
