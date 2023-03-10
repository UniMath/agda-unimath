# The Gaussian integers

```agda
module commutative-algebra.gaussian-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.identity-types
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.rings
```

</details>

## Idea

The Gaussian integers are the complex numbers of the form `a + bi`, where `a` and `b` are integers.

## Definition

### The underlying type of the Gaussian integers

```agda
ℤ[i] : UU lzero
ℤ[i] = ℤ × ℤ
```

### Observational equality of the Gaussian integers

```agda
Eq-ℤ[i] : ℤ[i] → ℤ[i] → UU lzero
Eq-ℤ[i] x y = (Id (pr1 x) (pr1 y)) × (Id (pr2 x) (pr2 y))

refl-Eq-ℤ[i] : (x : ℤ[i]) → Eq-ℤ[i] x x
pr1 (refl-Eq-ℤ[i] x) = refl
pr2 (refl-Eq-ℤ[i] x) = refl

Eq-eq-ℤ[i] : {x y : ℤ[i]} → Id x y → Eq-ℤ[i] x y
Eq-eq-ℤ[i] {x} refl = refl-Eq-ℤ[i] x

eq-Eq-ℤ[i]' : {x y : ℤ[i]} → Eq-ℤ[i] x y → Id x y
eq-Eq-ℤ[i]' {pair a b} {pair .a .b} (pair refl refl) = refl

eq-Eq-ℤ[i] : {x y : ℤ[i]} → Id (pr1 x) (pr1 y) → Id (pr2 x) (pr2 y) → Id x y
eq-Eq-ℤ[i] {pair a b} {pair .a .b} refl refl = refl
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

### The Gaussian integer `-i`.

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

ap-add-ℤ[i] :
  {x x' y y' : ℤ[i]} → Id x x' → Id y y' → Id (add-ℤ[i] x y) (add-ℤ[i] x' y')
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
pr1 (mul-ℤ[i] (a , b) (a' , b')) = diff-ℤ (mul-ℤ a a') (mul-ℤ b b')
pr2 (mul-ℤ[i] (a , b) (a' , b')) = mul-ℤ a b' +ℤ mul-ℤ a' b

ap-mul-ℤ[i] :
  {x x' y y' : ℤ[i]} → Id x x' → Id y y' → Id (mul-ℤ[i] x y) (mul-ℤ[i] x' y')
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
left-unit-law-add-ℤ[i] : (x : ℤ[i]) → Id (add-ℤ[i] zero-ℤ[i] x) x
left-unit-law-add-ℤ[i] (pair a b) = eq-Eq-ℤ[i] refl refl

right-unit-law-add-ℤ[i] : (x : ℤ[i]) → Id (add-ℤ[i] x zero-ℤ[i]) x
right-unit-law-add-ℤ[i] (pair a b) =
  eq-Eq-ℤ[i] (right-unit-law-add-ℤ a) (right-unit-law-add-ℤ b)

associative-add-ℤ[i] :
  (x y z : ℤ[i]) → Id (add-ℤ[i] (add-ℤ[i] x y) z) (add-ℤ[i] x (add-ℤ[i] y z))
associative-add-ℤ[i] (pair a1 b1) (pair a2 b2) (pair a3 b3) =
  eq-Eq-ℤ[i] (associative-add-ℤ a1 a2 a3) (associative-add-ℤ b1 b2 b3)

left-inverse-law-add-ℤ[i] :
  (x : ℤ[i]) → Id (add-ℤ[i] (neg-ℤ[i] x) x) zero-ℤ[i]
left-inverse-law-add-ℤ[i] (pair a b) =
  eq-Eq-ℤ[i] (left-inverse-law-add-ℤ a) (left-inverse-law-add-ℤ b)

right-inverse-law-add-ℤ[i] :
  (x : ℤ[i]) → Id (add-ℤ[i] x (neg-ℤ[i] x)) zero-ℤ[i]
right-inverse-law-add-ℤ[i] (pair a b) =
  eq-Eq-ℤ[i] (right-inverse-law-add-ℤ a) (right-inverse-law-add-ℤ b)

commutative-add-ℤ[i] :
  (x y : ℤ[i]) → Id (add-ℤ[i] x y) (add-ℤ[i] y x)
commutative-add-ℤ[i] (pair a b) (pair a' b') =
  eq-Eq-ℤ[i] (commutative-add-ℤ a a') (commutative-add-ℤ b b')

left-unit-law-mul-ℤ[i] : (x : ℤ[i]) → Id (mul-ℤ[i] one-ℤ[i] x) x
left-unit-law-mul-ℤ[i] (pair a b) =
  eq-Eq-ℤ[i]
    ( right-unit-law-add-ℤ a)
    ( ap (add-ℤ b) (right-zero-law-mul-ℤ a) ∙ right-unit-law-add-ℤ b)

right-unit-law-mul-ℤ[i] : (x : ℤ[i]) → Id (mul-ℤ[i] x one-ℤ[i]) x
right-unit-law-mul-ℤ[i] (pair a b) =
  eq-Eq-ℤ[i]
    ( ( ap-add-ℤ
        ( right-unit-law-mul-ℤ a)
        ( ap neg-ℤ (right-zero-law-mul-ℤ b))) ∙
      ( right-unit-law-add-ℤ a))
    ( ap (add-ℤ' b) (right-zero-law-mul-ℤ a))

commutative-mul-ℤ[i] :
  (x y : ℤ[i]) → Id (mul-ℤ[i] x y) (mul-ℤ[i] y x)
commutative-mul-ℤ[i] (pair a b) (pair c d) =
  eq-Eq-ℤ[i]
    ( ap-add-ℤ (commutative-mul-ℤ a c) (ap neg-ℤ (commutative-mul-ℤ b d)))
    ( commutative-add-ℤ (mul-ℤ a d) (mul-ℤ c b))

associative-mul-ℤ[i] :
  (x y z : ℤ[i]) → Id (mul-ℤ[i] (mul-ℤ[i] x y) z) (mul-ℤ[i] x (mul-ℤ[i] y z))
associative-mul-ℤ[i] (pair a b) (pair c d) (pair e f) =
  eq-Eq-ℤ[i]
    ( ( ap-add-ℤ
        ( ( right-distributive-mul-add-ℤ
            ( mul-ℤ a c)
            ( mul-ℤ neg-one-ℤ (mul-ℤ b d))
            ( e)) ∙
          ( ap-add-ℤ
            ( associative-mul-ℤ a c e)
            ( ( associative-mul-ℤ neg-one-ℤ (mul-ℤ b d) e) ∙
              ( ap
                ( mul-ℤ neg-one-ℤ)
                ( ( associative-mul-ℤ b d e) ∙
                  ( ap (mul-ℤ b) (commutative-mul-ℤ d e)))))))
        ( ( ap
            ( neg-ℤ)
            ( ( right-distributive-mul-add-ℤ (mul-ℤ a d) (mul-ℤ c b) f) ∙
              ( ap-add-ℤ
                ( associative-mul-ℤ a d f)
                ( associative-mul-ℤ c b f)))) ∙
          ( ( left-distributive-mul-add-ℤ
              ( neg-one-ℤ)
              ( mul-ℤ a (mul-ℤ d f))
              ( mul-ℤ c (mul-ℤ b f)))))) ∙
      ( ( interchange-law-add-add-ℤ
          ( mul-ℤ a (mul-ℤ c e))
          ( neg-ℤ (mul-ℤ b (mul-ℤ e d)))
          ( neg-ℤ (mul-ℤ a (mul-ℤ d f)))
          ( neg-ℤ (mul-ℤ c (mul-ℤ b f)))) ∙
        ( ap-add-ℤ
          ( ( ap-add-ℤ
              ( refl {x = mul-ℤ a (mul-ℤ c e)})
              ( inv
                ( right-negative-law-mul-ℤ a (mul-ℤ d f)))) ∙
            ( inv
              ( left-distributive-mul-add-ℤ a
                ( mul-ℤ c e)
                ( neg-ℤ (mul-ℤ d f)))))
          ( ( inv
              ( left-distributive-mul-add-ℤ
                ( neg-one-ℤ)
                ( mul-ℤ b (mul-ℤ e d))
                ( mul-ℤ c (mul-ℤ b f)))) ∙
            ( ap neg-ℤ
              ( ( ap-add-ℤ
                  ( refl {x = mul-ℤ b (mul-ℤ e d)})
                  ( ( ap (mul-ℤ c) (commutative-mul-ℤ b f)) ∙
                    ( ( inv (associative-mul-ℤ c f b)) ∙
                      ( commutative-mul-ℤ (mul-ℤ c f) b)))) ∙
                ( ( inv
                    ( left-distributive-mul-add-ℤ b
                      ( mul-ℤ e d)
                      ( mul-ℤ c f))) ∙
                  ( ap
                    ( mul-ℤ b)
                    ( commutative-add-ℤ (mul-ℤ e d) (mul-ℤ c f))))))))))
    ( ( ap-add-ℤ
        ( ( right-distributive-mul-add-ℤ
            ( mul-ℤ a c)
            ( neg-ℤ (mul-ℤ b d))
            ( f)) ∙
          ( ap
            ( add-ℤ (mul-ℤ (mul-ℤ a c) f))
            ( left-negative-law-mul-ℤ (mul-ℤ b d) f)))
        ( ( left-distributive-mul-add-ℤ e (mul-ℤ a d) (mul-ℤ c b)) ∙
          ( ap-add-ℤ
            ( ( commutative-mul-ℤ e (mul-ℤ a d)) ∙
              ( ( associative-mul-ℤ a d e) ∙
                ( ap (mul-ℤ a) (commutative-mul-ℤ d e))))
            ( ( inv (associative-mul-ℤ e c b)) ∙
              ( ap (mul-ℤ' b) (commutative-mul-ℤ e c)))))) ∙
      ( ( interchange-law-add-add-ℤ
          ( mul-ℤ (mul-ℤ a c) f)
          ( neg-ℤ (mul-ℤ (mul-ℤ b d) f))
          ( mul-ℤ a (mul-ℤ e d))
          ( mul-ℤ (mul-ℤ c e) b)) ∙
        ( ap-add-ℤ
          ( ( ap-add-ℤ
              ( associative-mul-ℤ a c f)
              ( refl)) ∙
            ( inv (left-distributive-mul-add-ℤ a (mul-ℤ c f) (mul-ℤ e d))))
          ( ( ap-add-ℤ
              ( ( ap
                  ( neg-ℤ)
                  ( ( associative-mul-ℤ b d f) ∙
                    ( commutative-mul-ℤ b (mul-ℤ d f)))) ∙
                ( inv (left-negative-law-mul-ℤ (mul-ℤ d f) b)))
              ( refl)) ∙
            ( ( inv
                ( ( right-distributive-mul-add-ℤ
                    ( neg-ℤ (mul-ℤ d f))
                    ( mul-ℤ c e) b))) ∙
              ( ap
                ( mul-ℤ' b)
                ( commutative-add-ℤ (neg-ℤ (mul-ℤ d f)) (mul-ℤ c e))))))))

left-distributive-mul-add-ℤ[i] :
  (x y z : ℤ[i]) →
  Id (mul-ℤ[i] x (add-ℤ[i] y z)) (add-ℤ[i] (mul-ℤ[i] x y) (mul-ℤ[i] x z))
left-distributive-mul-add-ℤ[i] (pair a b) (pair c d) (pair e f) =
  eq-Eq-ℤ[i]
    ( ( ap-add-ℤ
        ( left-distributive-mul-add-ℤ a c e)
        ( ( ap neg-ℤ (left-distributive-mul-add-ℤ b d f)) ∙
          ( left-distributive-mul-add-ℤ neg-one-ℤ (mul-ℤ b d) (mul-ℤ b f)))) ∙
      ( interchange-law-add-add-ℤ
        ( mul-ℤ a c)
        ( mul-ℤ a e)
        ( neg-ℤ (mul-ℤ b d))
        ( neg-ℤ (mul-ℤ b f))))
    ( ( ap-add-ℤ
        ( left-distributive-mul-add-ℤ a d f)
        ( right-distributive-mul-add-ℤ c e b)) ∙
      ( interchange-law-add-add-ℤ
        ( mul-ℤ a d)
        ( mul-ℤ a f)
        ( mul-ℤ c b)
        ( mul-ℤ e b)))

right-distributive-mul-add-ℤ[i] :
  (x y z : ℤ[i]) →
  Id (mul-ℤ[i] (add-ℤ[i] x y) z) (add-ℤ[i] (mul-ℤ[i] x z) (mul-ℤ[i] y z))
right-distributive-mul-add-ℤ[i] x y z =
  ( commutative-mul-ℤ[i] (add-ℤ[i] x y) z) ∙
  ( ( left-distributive-mul-add-ℤ[i] z x y) ∙
    ( ap-add-ℤ[i] (commutative-mul-ℤ[i] z x) (commutative-mul-ℤ[i] z y)))

ℤ[i]-Semigroup : Semigroup lzero
pr1 ℤ[i]-Semigroup = prod-Set ℤ-Set ℤ-Set
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
