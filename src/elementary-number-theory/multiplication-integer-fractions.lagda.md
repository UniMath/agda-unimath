# Multiplication on integer fractions

```agda
module elementary-number-theory.multiplication-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

**Multiplication on integer fractions** is an extension of the
[multiplicative operation](elementary-number-theory.multiplication-integers.md)
on the [integers](elementary-number-theory.integers.md) to
[integer fractions](elementary-number-theory.integer-fractions.md). Note that
the basic properties of multiplication on integer fraction only hold up to
fraction similarity.

## Definition

```agda
mul-fraction-ℤ : fraction-ℤ → fraction-ℤ → fraction-ℤ
pr1 (mul-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos)) =
  m *ℤ m'
pr1 (pr2 (mul-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) =
  n *ℤ n'
pr2 (pr2 (mul-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) =
  is-positive-mul-ℤ n-pos n'-pos

mul-fraction-ℤ' : fraction-ℤ → fraction-ℤ → fraction-ℤ
mul-fraction-ℤ' x y = mul-fraction-ℤ y x

infixl 40 _*fraction-ℤ_
_*fraction-ℤ_ = mul-fraction-ℤ

ap-mul-fraction-ℤ :
  {x y x' y' : fraction-ℤ} → x ＝ x' → y ＝ y' →
  x *fraction-ℤ y ＝ x' *fraction-ℤ y'
ap-mul-fraction-ℤ p q = ap-binary mul-fraction-ℤ p q
```

## Properties

### Multiplication respects the similarity relation

```agda
sim-fraction-mul-fraction-ℤ :
  {x x' y y' : fraction-ℤ} →
  sim-fraction-ℤ x x' →
  sim-fraction-ℤ y y' →
  sim-fraction-ℤ (x *fraction-ℤ y) (x' *fraction-ℤ y')
sim-fraction-mul-fraction-ℤ
  {(nx , dx , dxp)} {(nx' , dx' , dx'p)}
  {(ny , dy , dyp)} {(ny' , dy' , dy'p)} p q =
  equational-reasoning
    (nx *ℤ ny) *ℤ (dx' *ℤ dy')
    ＝ (nx *ℤ dx') *ℤ (ny *ℤ dy')
      by interchange-law-mul-mul-ℤ nx ny dx' dy'
    ＝ (nx' *ℤ dx) *ℤ (ny' *ℤ dy)
      by ap-mul-ℤ p q
    ＝ (nx' *ℤ ny') *ℤ (dx *ℤ dy)
      by interchange-law-mul-mul-ℤ nx' dx ny' dy
```

### Unit laws

```agda
left-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ one-fraction-ℤ k) k
left-unit-law-mul-fraction-ℤ k = refl

right-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ k one-fraction-ℤ) k
right-unit-law-mul-fraction-ℤ (n , d , p) =
  ap-mul-ℤ (right-unit-law-mul-ℤ n) (inv (right-unit-law-mul-ℤ d))
```

### Multiplication is associative

```agda
associative-mul-fraction-ℤ :
  (x y z : fraction-ℤ) →
  sim-fraction-ℤ
    (mul-fraction-ℤ (mul-fraction-ℤ x y) z)
    (mul-fraction-ℤ x (mul-fraction-ℤ y z))
associative-mul-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) (nz , dz , dzp) =
  ap-mul-ℤ (associative-mul-ℤ nx ny nz) (inv (associative-mul-ℤ dx dy dz))
```

### Multiplication is commutative

```agda
commutative-mul-fraction-ℤ :
  (x y : fraction-ℤ) → sim-fraction-ℤ (x *fraction-ℤ y) (y *fraction-ℤ x)
commutative-mul-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) =
  ap-mul-ℤ (commutative-mul-ℤ nx ny) (commutative-mul-ℤ dy dx)
```
