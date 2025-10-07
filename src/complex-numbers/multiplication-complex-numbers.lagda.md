# Multiplication of complex numbers

```agda
module complex-numbers.multiplication-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
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
      ( ( commutative-add-ℝ _ _) ∙
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
        ＝ ((a *ℝ c *ℝ e) -ℝ (b *ℝ d *ℝ e)) -ℝ ((a *ℝ d *ℝ f) +ℝ (b *ℝ c *ℝ f))
          by
            ap-diff-ℝ
              ( right-distributive-mul-diff-ℝ _ _ _)
              ( right-distributive-mul-add-ℝ _ _ _)
        ＝ (a *ℝ c *ℝ e -ℝ a *ℝ d *ℝ f) +ℝ (neg-ℝ (b *ℝ d *ℝ e) -ℝ b *ℝ c *ℝ f)
          by interchange-law-diff-add-ℝ _ _ _ _
        ＝ (a *ℝ c *ℝ e -ℝ a *ℝ d *ℝ f) -ℝ (b *ℝ c *ℝ f +ℝ b *ℝ d *ℝ e)
          by
            ap-add-ℝ
              ( refl)
              ( commutative-add-ℝ _ _ ∙ inv (distributive-neg-add-ℝ _ _))
        ＝ (a *ℝ (c *ℝ e) -ℝ a *ℝ (d *ℝ f)) -ℝ (b *ℝ (c *ℝ f) +ℝ b *ℝ (d *ℝ e))
          by
            ap-diff-ℝ
              ( ap-diff-ℝ (associative-mul-ℝ a c e) (associative-mul-ℝ a d f))
              ( ap-add-ℝ (associative-mul-ℝ b c f) (associative-mul-ℝ b d e))
        ＝ a *ℝ (c *ℝ e -ℝ d *ℝ f) -ℝ b *ℝ (c *ℝ f +ℝ d *ℝ e)
          by
            ap-diff-ℝ
              ( inv (left-distributive-mul-diff-ℝ _ _ _))
              ( inv (left-distributive-mul-add-ℝ _ _ _)))
      ( equational-reasoning
        (a *ℝ c -ℝ b *ℝ d) *ℝ f +ℝ (a *ℝ d +ℝ b *ℝ c) *ℝ e
        ＝ (a *ℝ c *ℝ f -ℝ b *ℝ d *ℝ f) +ℝ (a *ℝ d *ℝ e +ℝ b *ℝ c *ℝ e)
          by
            ap-add-ℝ
              ( right-distributive-mul-diff-ℝ _ _ _)
              ( right-distributive-mul-add-ℝ _ _ _)
        ＝ (a *ℝ c *ℝ f +ℝ a *ℝ d *ℝ e) +ℝ (neg-ℝ (b *ℝ d *ℝ f) +ℝ b *ℝ c *ℝ e)
          by interchange-law-add-add-ℝ _ _ _ _
        ＝ (a *ℝ c *ℝ f +ℝ a *ℝ d *ℝ e) +ℝ (b *ℝ c *ℝ e -ℝ b *ℝ d *ℝ f)
          by ap-add-ℝ refl (commutative-add-ℝ _ _)
        ＝ (a *ℝ (c *ℝ f) +ℝ a *ℝ (d *ℝ e)) +ℝ (b *ℝ (c *ℝ e) -ℝ b *ℝ (d *ℝ f))
          by
            ap-add-ℝ
              ( ap-add-ℝ (associative-mul-ℝ a c f) (associative-mul-ℝ a d e))
              ( ap-diff-ℝ (associative-mul-ℝ b c e) (associative-mul-ℝ b d f))
        ＝ a *ℝ (c *ℝ f +ℝ d *ℝ e) +ℝ b *ℝ (c *ℝ e -ℝ d *ℝ f)
          by
            ap-add-ℝ
              ( inv (left-distributive-mul-add-ℝ _ _ _))
              ( inv (left-distributive-mul-diff-ℝ _ _ _)))
```

### Unit laws of multiplication

```agda
abstract
  left-unit-law-mul-ℂ : {l : Level} → (z : ℂ l) → mul-ℂ one-ℂ z ＝ z
  left-unit-law-mul-ℂ (a , b) =
    eq-ℂ
      ( equational-reasoning
        one-ℝ *ℝ a -ℝ zero-ℝ *ℝ b
        ＝ a -ℝ zero-ℝ
          by
            eq-sim-ℝ
              ( preserves-sim-diff-ℝ
                ( sim-eq-ℝ (left-unit-law-mul-ℝ a))
                ( left-zero-law-mul-ℝ b))
        ＝ a
          by right-unit-law-diff-ℝ a)
      ( equational-reasoning
        one-ℝ *ℝ b +ℝ zero-ℝ *ℝ a
        ＝ b +ℝ zero-ℝ
          by
            eq-sim-ℝ
              ( preserves-sim-add-ℝ
                ( sim-eq-ℝ (left-unit-law-mul-ℝ b))
                ( left-zero-law-mul-ℝ a))
        ＝ b
          by right-unit-law-add-ℝ b)

  right-unit-law-mul-ℂ : {l : Level} → (z : ℂ l) → mul-ℂ z one-ℂ ＝ z
  right-unit-law-mul-ℂ z = commutative-mul-ℂ _ _ ∙ left-unit-law-mul-ℂ z
```

### Multiplication is distributive over addition

```agda
abstract
  left-distributive-mul-add-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    x *ℂ (y +ℂ z) ＝ x *ℂ y +ℂ x *ℂ z
  left-distributive-mul-add-ℂ (a , b) (c , d) (e , f) =
    eq-ℂ
      ( equational-reasoning
        a *ℝ (c +ℝ e) -ℝ b *ℝ (d +ℝ f)
        ＝ (a *ℝ c +ℝ a *ℝ e) -ℝ (b *ℝ d +ℝ b *ℝ f)
          by
            ap-diff-ℝ
              ( left-distributive-mul-add-ℝ a c e)
              ( left-distributive-mul-add-ℝ b d f)
        ＝ (a *ℝ c -ℝ b *ℝ d) +ℝ (a *ℝ e -ℝ b *ℝ f)
          by interchange-law-diff-add-ℝ _ _ _ _)
      ( equational-reasoning
        a *ℝ (d +ℝ f) +ℝ b *ℝ (c +ℝ e)
        ＝ (a *ℝ d +ℝ a *ℝ f) +ℝ (b *ℝ c +ℝ b *ℝ e)
          by
            ap-add-ℝ
              ( left-distributive-mul-add-ℝ a d f)
              ( left-distributive-mul-add-ℝ b c e)
        ＝ (a *ℝ d +ℝ b *ℝ c) +ℝ (a *ℝ f +ℝ b *ℝ e)
          by interchange-law-add-add-ℝ _ _ _ _)

  right-distributive-mul-add-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    (x +ℂ y) *ℂ z ＝ x *ℂ z +ℂ y *ℂ z
  right-distributive-mul-add-ℂ x y z =
    equational-reasoning
      (x +ℂ y) *ℂ z
      ＝ z *ℂ (x +ℂ y)
        by commutative-mul-ℂ _ _
      ＝ z *ℂ x +ℂ z *ℂ y
        by left-distributive-mul-add-ℂ z x y
      ＝ x *ℂ z +ℂ y *ℂ z
        by ap-add-ℂ (commutative-mul-ℂ z x) (commutative-mul-ℂ z y)
```

### Zero laws of multiplication

```agda
abstract
  left-zero-law-mul-ℂ : {l : Level} → (z : ℂ l) → sim-ℂ (zero-ℂ *ℂ z) zero-ℂ
  left-zero-law-mul-ℂ (a , b) =
    ( ( similarity-reasoning-ℝ
          zero-ℝ *ℝ a -ℝ zero-ℝ *ℝ b
          ~ℝ zero-ℝ -ℝ zero-ℝ
            by
              preserves-sim-diff-ℝ
                ( left-zero-law-mul-ℝ a)
                ( left-zero-law-mul-ℝ b)
          ~ℝ zero-ℝ
            by sim-eq-ℝ (right-unit-law-diff-ℝ zero-ℝ)) ,
      ( similarity-reasoning-ℝ
          zero-ℝ *ℝ b +ℝ zero-ℝ *ℝ a
          ~ℝ zero-ℝ +ℝ zero-ℝ
            by
              preserves-sim-add-ℝ
                ( left-zero-law-mul-ℝ b)
                ( left-zero-law-mul-ℝ a)
          ~ℝ zero-ℝ
            by sim-eq-ℝ (right-unit-law-add-ℝ zero-ℝ)))

  right-zero-law-mul-ℂ : {l : Level} → (z : ℂ l) → sim-ℂ (z *ℂ zero-ℂ) zero-ℂ
  right-zero-law-mul-ℂ z =
    tr
      ( λ w → sim-ℂ w zero-ℂ)
      ( commutative-mul-ℂ _ _)
      ( left-zero-law-mul-ℂ z)
```
