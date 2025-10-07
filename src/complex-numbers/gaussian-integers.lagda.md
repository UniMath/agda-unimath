# The Gaussian integers

```agda
module complex-numbers.gaussian-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "Gaussian integers" WDID=Q724975 WD="Gaussian integer" Agda="ℤ[i]"}}
are the [complex numbers](complex-numbers.complex-numbers.md) of the form
`a + bi`, where `a` and `b` are
[integers](elementary-number-theory.integers.md).

## Definition

### The underlying type of the Gaussian integers

```agda
ℤ[i] : UU lzero
ℤ[i] = ℤ × ℤ
```

### Observational equality of the Gaussian integers

```agda
Eq-ℤ[i] : ℤ[i] → ℤ[i] → UU lzero
Eq-ℤ[i] x y = (pr1 x ＝ pr1 y) × (pr2 x ＝ pr2 y)

refl-Eq-ℤ[i] : (x : ℤ[i]) → Eq-ℤ[i] x x
pr1 (refl-Eq-ℤ[i] x) = refl
pr2 (refl-Eq-ℤ[i] x) = refl

Eq-eq-ℤ[i] : {x y : ℤ[i]} → x ＝ y → Eq-ℤ[i] x y
Eq-eq-ℤ[i] {x} refl = refl-Eq-ℤ[i] x

eq-Eq-ℤ[i]' : {x y : ℤ[i]} → Eq-ℤ[i] x y → x ＝ y
eq-Eq-ℤ[i]' {a , b} {.a , .b} (refl , refl) = refl

eq-Eq-ℤ[i] : {x y : ℤ[i]} → pr1 x ＝ pr1 y → pr2 x ＝ pr2 y → x ＝ y
eq-Eq-ℤ[i] {a , b} {.a , .b} refl refl = refl
```

### The Gaussian integer zero

```agda
zero-ℤ[i] : ℤ[i]
pr1 zero-ℤ[i] = zero-ℤ
pr2 zero-ℤ[i] = zero-ℤ
```

### The Gaussian integer one

```agda
one-ℤ[i] : ℤ[i]
pr1 one-ℤ[i] = one-ℤ
pr2 one-ℤ[i] = zero-ℤ
```

### The inclusion of the integers into the Gaussian integers

```agda
gaussian-int-ℤ : ℤ → ℤ[i]
pr1 (gaussian-int-ℤ x) = x
pr2 (gaussian-int-ℤ x) = zero-ℤ
```

### The Gaussian integer `i`

```agda
i-ℤ[i] : ℤ[i]
pr1 i-ℤ[i] = zero-ℤ
pr2 i-ℤ[i] = one-ℤ
```

### The Gaussian integer `-i`

```agda
neg-i-ℤ[i] : ℤ[i]
pr1 neg-i-ℤ[i] = zero-ℤ
pr2 neg-i-ℤ[i] = neg-one-ℤ
```

### Addition of Gaussian integers

```agda
add-ℤ[i] : ℤ[i] → ℤ[i] → ℤ[i]
pr1 (add-ℤ[i] (a , b) (a' , b')) = a +ℤ a'
pr2 (add-ℤ[i] (a , b) (a' , b')) = b +ℤ b'

infixl 35 _+ℤ[i]_
_+ℤ[i]_ = add-ℤ[i]

ap-add-ℤ[i] :
  {x x' y y' : ℤ[i]} → x ＝ x' → y ＝ y' → x +ℤ[i] y ＝ x' +ℤ[i] y'
ap-add-ℤ[i] p q = ap-binary add-ℤ[i] p q
```

### Negatives of Gaussian integers

```agda
neg-ℤ[i] : ℤ[i] → ℤ[i]
pr1 (neg-ℤ[i] (a , b)) = neg-ℤ a
pr2 (neg-ℤ[i] (a , b)) = neg-ℤ b
```

### Multiplication of Gaussian integers

```agda
mul-ℤ[i] : ℤ[i] → ℤ[i] → ℤ[i]
pr1 (mul-ℤ[i] (a , b) (a' , b')) = (a *ℤ a') -ℤ (b *ℤ b')
pr2 (mul-ℤ[i] (a , b) (a' , b')) = (a *ℤ b') +ℤ (a' *ℤ b)

infixl 40 _*ℤ[i]_
_*ℤ[i]_ = mul-ℤ[i]

ap-mul-ℤ[i] :
  {x x' y y' : ℤ[i]} → x ＝ x' → y ＝ y' → x *ℤ[i] y ＝ x' *ℤ[i] y'
ap-mul-ℤ[i] p q = ap-binary mul-ℤ[i] p q
```

### Conjugation of Gaussian integers

```agda
conjugate-ℤ[i] : ℤ[i] → ℤ[i]
pr1 (conjugate-ℤ[i] (a , b)) = a
pr2 (conjugate-ℤ[i] (a , b)) = neg-ℤ b
```

### The Gaussian integers form a commutative ring

```agda
left-unit-law-add-ℤ[i] : (x : ℤ[i]) → zero-ℤ[i] +ℤ[i] x ＝ x
left-unit-law-add-ℤ[i] (a , b) = eq-Eq-ℤ[i] refl refl

right-unit-law-add-ℤ[i] : (x : ℤ[i]) → x +ℤ[i] zero-ℤ[i] ＝ x
right-unit-law-add-ℤ[i] (a , b) =
  eq-Eq-ℤ[i] (right-unit-law-add-ℤ a) (right-unit-law-add-ℤ b)

associative-add-ℤ[i] :
  (x y z : ℤ[i]) → (x +ℤ[i] y) +ℤ[i] z ＝ x +ℤ[i] (y +ℤ[i] z)
associative-add-ℤ[i] (a1 , b1) (a2 , b2) (a3 , b3) =
  eq-Eq-ℤ[i] (associative-add-ℤ a1 a2 a3) (associative-add-ℤ b1 b2 b3)

left-inverse-law-add-ℤ[i] :
  (x : ℤ[i]) → (neg-ℤ[i] x) +ℤ[i] x ＝ zero-ℤ[i]
left-inverse-law-add-ℤ[i] (a , b) =
  eq-Eq-ℤ[i] (left-inverse-law-add-ℤ a) (left-inverse-law-add-ℤ b)

right-inverse-law-add-ℤ[i] :
  (x : ℤ[i]) → x +ℤ[i] (neg-ℤ[i] x) ＝ zero-ℤ[i]
right-inverse-law-add-ℤ[i] (a , b) =
  eq-Eq-ℤ[i] (right-inverse-law-add-ℤ a) (right-inverse-law-add-ℤ b)

commutative-add-ℤ[i] :
  (x y : ℤ[i]) → x +ℤ[i] y ＝ y +ℤ[i] x
commutative-add-ℤ[i] (a , b) (a' , b') =
  eq-Eq-ℤ[i] (commutative-add-ℤ a a') (commutative-add-ℤ b b')

left-unit-law-mul-ℤ[i] : (x : ℤ[i]) → one-ℤ[i] *ℤ[i] x ＝ x
left-unit-law-mul-ℤ[i] (a , b) =
  eq-Eq-ℤ[i]
    ( right-unit-law-add-ℤ a)
    ( ap (b +ℤ_) (right-zero-law-mul-ℤ a) ∙ right-unit-law-add-ℤ b)

right-unit-law-mul-ℤ[i] : (x : ℤ[i]) → x *ℤ[i] one-ℤ[i] ＝ x
right-unit-law-mul-ℤ[i] (a , b) =
  eq-Eq-ℤ[i]
    ( ( ap-add-ℤ
        ( right-unit-law-mul-ℤ a)
        ( ap neg-ℤ (right-zero-law-mul-ℤ b))) ∙
      ( right-unit-law-add-ℤ a))
    ( ap (_+ℤ b) (right-zero-law-mul-ℤ a))

commutative-mul-ℤ[i] :
  (x y : ℤ[i]) → x *ℤ[i] y ＝ y *ℤ[i] x
commutative-mul-ℤ[i] (a , b) (c , d) =
  eq-Eq-ℤ[i]
    ( ap-add-ℤ (commutative-mul-ℤ a c) (ap neg-ℤ (commutative-mul-ℤ b d)))
    ( commutative-add-ℤ (a *ℤ d) (c *ℤ b))

associative-mul-ℤ[i] :
  (x y z : ℤ[i]) → (x *ℤ[i] y) *ℤ[i] z ＝ x *ℤ[i] (y *ℤ[i] z)
associative-mul-ℤ[i] (a , b) (c , d) (e , f) =
  eq-Eq-ℤ[i]
    ( ( ap-add-ℤ
        ( ( right-distributive-mul-add-ℤ
            ( a *ℤ c)
            ( neg-one-ℤ *ℤ (b *ℤ d))
            ( e)) ∙
          ( ap-add-ℤ
            ( associative-mul-ℤ a c e)
            ( ( associative-mul-ℤ neg-one-ℤ (b *ℤ d) e) ∙
              ( ap
                ( neg-one-ℤ *ℤ_)
                ( ( associative-mul-ℤ b d e) ∙
                  ( ap (b *ℤ_) (commutative-mul-ℤ d e)))))))
        ( ( ap
            ( neg-ℤ)
            ( ( right-distributive-mul-add-ℤ (a *ℤ d) (c *ℤ b) f) ∙
              ( ap-add-ℤ
                ( associative-mul-ℤ a d f)
                ( associative-mul-ℤ c b f)))) ∙
          ( ( left-distributive-mul-add-ℤ
              ( neg-one-ℤ)
              ( a *ℤ (d *ℤ f))
              ( c *ℤ (b *ℤ f)))))) ∙
      ( ( interchange-law-add-add-ℤ
          ( a *ℤ (c *ℤ e))
          ( neg-ℤ (b *ℤ (e *ℤ d)))
          ( neg-ℤ (a *ℤ (d *ℤ f)))
          ( neg-ℤ (c *ℤ (b *ℤ f)))) ∙
        ( ap-add-ℤ
          ( ( ap-add-ℤ
              ( refl {x = a *ℤ (c *ℤ e)})
              ( inv
                ( right-negative-law-mul-ℤ a (d *ℤ f)))) ∙
            ( inv
              ( left-distributive-mul-add-ℤ a
                ( c *ℤ e)
                ( neg-ℤ (d *ℤ f)))))
          ( ( inv
              ( left-distributive-mul-add-ℤ
                ( neg-one-ℤ)
                ( b *ℤ (e *ℤ d))
                ( c *ℤ (b *ℤ f)))) ∙
            ( ap neg-ℤ
              ( ( ap-add-ℤ
                  ( refl {x = b *ℤ (e *ℤ d)})
                  ( ( ap (c *ℤ_) (commutative-mul-ℤ b f)) ∙
                    ( ( inv (associative-mul-ℤ c f b)) ∙
                      ( commutative-mul-ℤ (c *ℤ f) b)))) ∙
                ( ( inv
                    ( left-distributive-mul-add-ℤ b
                      ( e *ℤ d)
                      ( c *ℤ f))) ∙
                  ( ap
                    ( b *ℤ_)
                    ( commutative-add-ℤ (e *ℤ d) (c *ℤ f))))))))))
    ( ( ap-add-ℤ
        ( ( right-distributive-mul-add-ℤ
            ( a *ℤ c)
            ( neg-ℤ (b *ℤ d))
            ( f)) ∙
          ( ap
            ( ((a *ℤ c) *ℤ f) +ℤ_)
            ( left-negative-law-mul-ℤ (b *ℤ d) f)))
        ( ( left-distributive-mul-add-ℤ e (a *ℤ d) (c *ℤ b)) ∙
          ( ap-add-ℤ
            ( ( commutative-mul-ℤ e (a *ℤ d)) ∙
              ( ( associative-mul-ℤ a d e) ∙
                ( ap (a *ℤ_) (commutative-mul-ℤ d e))))
            ( ( inv (associative-mul-ℤ e c b)) ∙
              ( ap (_*ℤ b) (commutative-mul-ℤ e c)))))) ∙
      ( ( interchange-law-add-add-ℤ
          ( (a *ℤ c) *ℤ f)
          ( neg-ℤ ((b *ℤ d) *ℤ f))
          ( a *ℤ (e *ℤ d))
          ( (c *ℤ e) *ℤ b)) ∙
        ( ap-add-ℤ
          ( ( ap-add-ℤ
              ( associative-mul-ℤ a c f)
              ( refl)) ∙
            ( inv (left-distributive-mul-add-ℤ a (c *ℤ f) (e *ℤ d))))
          ( ( ap-add-ℤ
              ( ( ap
                  ( neg-ℤ)
                  ( ( associative-mul-ℤ b d f) ∙
                    ( commutative-mul-ℤ b (d *ℤ f)))) ∙
                ( inv (left-negative-law-mul-ℤ (d *ℤ f) b)))
              ( refl)) ∙
            ( ( inv
                ( ( right-distributive-mul-add-ℤ
                    ( neg-ℤ (d *ℤ f))
                    ( c *ℤ e) b))) ∙
              ( ap
                ( _*ℤ b)
                ( commutative-add-ℤ (neg-ℤ (d *ℤ f)) (c *ℤ e))))))))

left-distributive-mul-add-ℤ[i] :
  (x y z : ℤ[i]) →
  x *ℤ[i] (y +ℤ[i] z) ＝ (x *ℤ[i] y) +ℤ[i] (x *ℤ[i] z)
left-distributive-mul-add-ℤ[i] (a , b) (c , d) (e , f) =
  eq-Eq-ℤ[i]
    ( ( ap-add-ℤ
        ( left-distributive-mul-add-ℤ a c e)
        ( ( ap neg-ℤ (left-distributive-mul-add-ℤ b d f)) ∙
          ( left-distributive-mul-add-ℤ neg-one-ℤ (b *ℤ d) (b *ℤ f)))) ∙
      ( interchange-law-add-add-ℤ
        ( a *ℤ c)
        ( a *ℤ e)
        ( neg-ℤ (b *ℤ d))
        ( neg-ℤ (b *ℤ f))))
    ( ( ap-add-ℤ
        ( left-distributive-mul-add-ℤ a d f)
        ( right-distributive-mul-add-ℤ c e b)) ∙
      ( interchange-law-add-add-ℤ
        ( a *ℤ d)
        ( a *ℤ f)
        ( c *ℤ b)
        ( e *ℤ b)))

right-distributive-mul-add-ℤ[i] :
  (x y z : ℤ[i]) →
  (x +ℤ[i] y) *ℤ[i] z ＝ (x *ℤ[i] z) +ℤ[i] (y *ℤ[i] z)
right-distributive-mul-add-ℤ[i] x y z =
  ( commutative-mul-ℤ[i] (x +ℤ[i] y) z) ∙
  ( ( left-distributive-mul-add-ℤ[i] z x y) ∙
    ( ap-add-ℤ[i] (commutative-mul-ℤ[i] z x) (commutative-mul-ℤ[i] z y)))

ℤ[i]-Semigroup : Semigroup lzero
pr1 ℤ[i]-Semigroup = product-Set ℤ-Set ℤ-Set
pr1 (pr2 ℤ[i]-Semigroup) = add-ℤ[i]
pr2 (pr2 ℤ[i]-Semigroup) = associative-add-ℤ[i]

ℤ[i]-Group : Group lzero
pr1 ℤ[i]-Group = ℤ[i]-Semigroup
pr1 (pr1 (pr2 ℤ[i]-Group)) = zero-ℤ[i]
pr1 (pr2 (pr1 (pr2 ℤ[i]-Group))) = left-unit-law-add-ℤ[i]
pr2 (pr2 (pr1 (pr2 ℤ[i]-Group))) = right-unit-law-add-ℤ[i]
pr1 (pr2 (pr2 ℤ[i]-Group)) = neg-ℤ[i]
pr1 (pr2 (pr2 (pr2 ℤ[i]-Group))) = left-inverse-law-add-ℤ[i]
pr2 (pr2 (pr2 (pr2 ℤ[i]-Group))) = right-inverse-law-add-ℤ[i]

ℤ[i]-Ab : Ab lzero
pr1 ℤ[i]-Ab = ℤ[i]-Group
pr2 ℤ[i]-Ab = commutative-add-ℤ[i]

ℤ[i]-Ring : Ring lzero
pr1 ℤ[i]-Ring = ℤ[i]-Ab
pr1 (pr1 (pr2 ℤ[i]-Ring)) = mul-ℤ[i]
pr2 (pr1 (pr2 ℤ[i]-Ring)) = associative-mul-ℤ[i]
pr1 (pr1 (pr2 (pr2 ℤ[i]-Ring))) = one-ℤ[i]
pr1 (pr2 (pr1 (pr2 (pr2 ℤ[i]-Ring)))) = left-unit-law-mul-ℤ[i]
pr2 (pr2 (pr1 (pr2 (pr2 ℤ[i]-Ring)))) = right-unit-law-mul-ℤ[i]
pr1 (pr2 (pr2 (pr2 ℤ[i]-Ring))) = left-distributive-mul-add-ℤ[i]
pr2 (pr2 (pr2 (pr2 ℤ[i]-Ring))) = right-distributive-mul-add-ℤ[i]

ℤ[i]-Commutative-Ring : Commutative-Ring lzero
pr1 ℤ[i]-Commutative-Ring = ℤ[i]-Ring
pr2 ℤ[i]-Commutative-Ring = commutative-mul-ℤ[i]
```
