# Multiplication of complex numbers

```agda
module complex-numbers.multiplication-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers
open import complex-numbers.similarity-complex-numbers

open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
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

ap-mul-ℂ :
  {l1 l2 : Level} {z z' : ℂ l1} → z ＝ z' → {w w' : ℂ l2} → w ＝ w' →
  mul-ℂ z w ＝ mul-ℂ z' w'
ap-mul-ℂ = ap-binary mul-ℂ
```

## Properties

### Multiplication is commutative

```agda
abstract
  commutative-mul-ℂ : {l1 l2 : Level} (x : ℂ l1) (y : ℂ l2) → x *ℂ y ＝ y *ℂ x
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
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
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
  left-unit-law-mul-ℂ : {l : Level} (z : ℂ l) → mul-ℂ one-ℂ z ＝ z
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

  right-unit-law-mul-ℂ : {l : Level} (z : ℂ l) → mul-ℂ z one-ℂ ＝ z
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
  left-zero-law-mul-ℂ : {l : Level} (z : ℂ l) → sim-ℂ (zero-ℂ *ℂ z) zero-ℂ
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

  right-zero-law-mul-ℂ : {l : Level} (z : ℂ l) → sim-ℂ (z *ℂ zero-ℂ) zero-ℂ
  right-zero-law-mul-ℂ z =
    tr
      ( λ w → sim-ℂ w zero-ℂ)
      ( commutative-mul-ℂ _ _)
      ( left-zero-law-mul-ℂ z)
```

### `i² = -1`

```agda
opaque
  unfolding neg-ℚ

  eq-neg-one-i²-ℂ : i-ℂ *ℂ i-ℂ ＝ neg-one-ℂ
  eq-neg-one-i²-ℂ =
    eq-ℂ
      ( equational-reasoning
        zero-ℝ *ℝ zero-ℝ -ℝ one-ℝ *ℝ one-ℝ
        ＝ zero-ℝ -ℝ one-ℝ
          by
            ap-diff-ℝ
              ( eq-sim-ℝ (left-zero-law-mul-ℝ zero-ℝ))
              ( left-unit-law-mul-ℝ one-ℝ)
        ＝ neg-ℝ one-ℝ
          by left-unit-law-add-ℝ _
        ＝ real-ℚ neg-one-ℚ
          by eq-neg-one-ℝ)
      ( equational-reasoning
        zero-ℝ *ℝ one-ℝ +ℝ one-ℝ *ℝ zero-ℝ
        ＝ zero-ℝ +ℝ zero-ℝ
          by
            eq-sim-ℝ
              ( preserves-sim-add-ℝ
                ( left-zero-law-mul-ℝ _)
                ( right-zero-law-mul-ℝ _))
        ＝ zero-ℝ
          by left-unit-law-add-ℝ zero-ℝ)
```

### The canonical embedding of real numbers in the complex numbers preserves multiplication

```agda
abstract
  mul-complex-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) →
    complex-ℝ x *ℂ complex-ℝ y ＝ complex-ℝ (x *ℝ y)
  mul-complex-ℝ {l1} {l2} x y =
    eq-ℂ
      ( equational-reasoning
        x *ℝ y -ℝ raise-ℝ l1 zero-ℝ *ℝ raise-ℝ l2 zero-ℝ
        ＝ x *ℝ y -ℝ zero-ℝ *ℝ zero-ℝ
          by
            eq-sim-ℝ
              ( preserves-sim-diff-ℝ
                ( refl-sim-ℝ (x *ℝ y))
                ( symmetric-sim-ℝ
                  ( preserves-sim-mul-ℝ (sim-raise-ℝ _ _) (sim-raise-ℝ _ _))))
        ＝ x *ℝ y -ℝ zero-ℝ
          by ap-diff-ℝ refl (eq-sim-ℝ (right-zero-law-mul-ℝ _))
        ＝ x *ℝ y
          by right-unit-law-diff-ℝ (x *ℝ y))
      ( eq-sim-ℝ
        ( similarity-reasoning-ℝ
          x *ℝ raise-ℝ l2 zero-ℝ +ℝ raise-ℝ l1 zero-ℝ *ℝ y
          ~ℝ x *ℝ zero-ℝ +ℝ zero-ℝ *ℝ y
            by
              symmetric-sim-ℝ
                ( preserves-sim-add-ℝ
                  ( preserves-sim-left-mul-ℝ _ _ _ (sim-raise-ℝ l2 zero-ℝ))
                  ( preserves-sim-right-mul-ℝ _ _ _ (sim-raise-ℝ l1 zero-ℝ)))
          ~ℝ zero-ℝ +ℝ zero-ℝ
            by
              preserves-sim-add-ℝ
                ( right-zero-law-mul-ℝ x)
                ( left-zero-law-mul-ℝ y)
          ~ℝ zero-ℝ
            by sim-eq-ℝ (left-unit-law-add-ℝ zero-ℝ)
          ~ℝ raise-ℝ (l1 ⊔ l2) zero-ℝ
            by sim-raise-ℝ (l1 ⊔ l2) zero-ℝ))
```

### Similarity is preserved by multiplication

```agda
abstract
  preserves-sim-mul-ℂ :
    {l1 l2 l3 l4 : Level} {x : ℂ l1} {x' : ℂ l2} {y : ℂ l3} {y' : ℂ l4} →
    sim-ℂ x x' → sim-ℂ y y' → sim-ℂ (x *ℂ y) (x' *ℂ y')
  preserves-sim-mul-ℂ (a~a' , b~b') (c~c' , d~d') =
    ( preserves-sim-diff-ℝ
        ( preserves-sim-mul-ℝ a~a' c~c')
        ( preserves-sim-mul-ℝ b~b' d~d') ,
      preserves-sim-add-ℝ
        ( preserves-sim-mul-ℝ a~a' d~d')
        ( preserves-sim-mul-ℝ b~b' c~c'))
```

### Negative laws of multiplication

```agda
abstract
  left-negative-law-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) →
    neg-ℂ z *ℂ w ＝ neg-ℂ (z *ℂ w)
  left-negative-law-mul-ℂ (a +iℂ b) (c +iℂ d) =
    inv
      ( eq-ℂ
        ( equational-reasoning
          neg-ℝ (a *ℝ c -ℝ b *ℝ d)
          ＝ neg-ℝ (a *ℝ c) -ℝ neg-ℝ (b *ℝ d)
            by distributive-neg-add-ℝ _ _
          ＝ neg-ℝ a *ℝ c -ℝ neg-ℝ b *ℝ d
            by
              ap-diff-ℝ
                ( inv (left-negative-law-mul-ℝ a c))
                ( inv (left-negative-law-mul-ℝ b d)))
        ( equational-reasoning
          neg-ℝ (a *ℝ d +ℝ b *ℝ c)
          ＝ neg-ℝ (a *ℝ d) +ℝ neg-ℝ (b *ℝ c)
            by distributive-neg-add-ℝ _ _
          ＝ neg-ℝ a *ℝ d +ℝ neg-ℝ b *ℝ c
            by
              ap-add-ℝ
                ( inv (left-negative-law-mul-ℝ a d))
                ( inv (left-negative-law-mul-ℝ b c))))

  right-negative-law-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) →
    z *ℂ neg-ℂ w ＝ neg-ℂ (z *ℂ w)
  right-negative-law-mul-ℂ z w =
    equational-reasoning
      z *ℂ neg-ℂ w
      ＝ neg-ℂ w *ℂ z
        by commutative-mul-ℂ _ _
      ＝ neg-ℂ (w *ℂ z)
        by left-negative-law-mul-ℂ w z
      ＝ neg-ℂ (z *ℂ w)
        by ap neg-ℂ (commutative-mul-ℂ w z)
```

### Raised unit laws

```agda
abstract
  left-raise-one-law-mul-ℂ :
    {l : Level} (z : ℂ l) → raise-ℂ l one-ℂ *ℂ z ＝ z
  left-raise-one-law-mul-ℂ {l} z =
    eq-sim-ℂ
      ( tr
        ( sim-ℂ (raise-ℂ l one-ℂ *ℂ z))
        ( left-unit-law-mul-ℂ z)
        ( preserves-sim-mul-ℂ (sim-raise-ℂ' l one-ℂ) (refl-sim-ℂ z)))

  right-raise-one-law-mul-ℂ :
    {l : Level} (z : ℂ l) → z *ℂ raise-ℂ l one-ℂ ＝ z
  right-raise-one-law-mul-ℂ z =
    commutative-mul-ℂ _ _ ∙ left-raise-one-law-mul-ℂ z
```

### Conjugation laws

```agda
abstract
  conjugate-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) →
    conjugate-ℂ (z *ℂ w) ＝ conjugate-ℂ z *ℂ conjugate-ℂ w
  conjugate-mul-ℂ (a +iℂ b) (c +iℂ d) =
    eq-ℂ
      ( ap-diff-ℝ refl (inv (negative-law-mul-ℝ b d)))
      ( ( distributive-neg-add-ℝ _ _) ∙
        ( inv
          ( ap-add-ℝ
            ( right-negative-law-mul-ℝ a d)
            ( left-negative-law-mul-ℝ b c))))
```

### Swapping laws

```agda
abstract
  left-swap-mul-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    x *ℂ (y *ℂ z) ＝ y *ℂ (x *ℂ z)
  left-swap-mul-ℂ x y z =
    ( inv (associative-mul-ℂ x y z)) ∙
    ( ap-mul-ℂ (commutative-mul-ℂ x y) refl) ∙
    ( associative-mul-ℂ y x z)
```
