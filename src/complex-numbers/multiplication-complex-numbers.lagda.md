# Multiplication of complex numbers

```agda
module complex-numbers.multiplication-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.multiplication-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.difference-real-numbers
```

</details>

## Idea

We introduce
{{#concept "multiplication" Disambiguation="complex numbers" Agda=mul-ℂ}} on the
[complex numbers](complex-numbers.complex-numbers.md) by the rule
`(a + bi)(c + di) = (ac - bd) + (ad + bc)i`.

## Definition

```agda
mul-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → ℂ (l1 ⊔ l2)
mul-ℂ (a , b) (c , d) = (a *ℝ c -ℝ b *ℝ d , a *ℝ d +ℝ b *ℝ c)

infixl 40 _*ℂ_
_*ℂ_ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → ℂ (l1 ⊔ l2)
_*ℂ_ = mul-ℂ
```

## Properties

### Multiplication is commutative

```agda
abstract
  commutative-mul-ℂ : {l1 l2 : Level} → (x : ℂ l1) (y : ℂ l2) → x *ℂ y ＝ y *ℂ x
  commutative-mul-ℂ (a , b) (c , d) =
    eq-ℂ
      ( ap-diff-ℝ (commutative-mul-ℝ a c) (commutative-mul-ℝ b d))
      ( ( commutative-add-ℝ _ _ ) ∙
        ( ap-add-ℝ (commutative-mul-ℝ b c) (commutative-mul-ℝ a d)))
```

### Multiplication is associative

```agda
abstract
  associative-mul-ℂ :
    {l1 l2 l3 : Level} → (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    (x *ℂ y) *ℂ z ＝ x *ℂ (y *ℂ z)
  associative-mul-ℂ (a , b) (c , d) (e , f) =
    eq-ℂ
      ( equational-reasoning
        (a *ℝ c -ℝ b *ℝ d) *ℝ e -ℝ (a *ℝ d +ℝ b *ℝ c) *ℝ f
        ＝ {!   !}
          by ap-diff-ℝ {!  right-distributive-mul-diff-ℝ !} {!   !}
        ＝ a *ℝ (c *ℝ e -ℝ d *ℝ f) -ℝ b *ℝ (c *ℝ f +ℝ d *ℝ e) by {!   !})
      {!   !}
```
