# Addition on integer fractions

```agda
module elementary-number-theory.multiplication-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

We introduce multiplication on integer fractions and derive its basic properties. Note
that the properties only hold up to fraction similarity.

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

infix 30 _*fraction-ℤ_
_*fraction-ℤ_ = mul-fraction-ℤ

ap-mul-fraction-ℤ :
  {x y x' y' : fraction-ℤ} → x ＝ x' → y ＝ y' →
  x *fraction-ℤ y ＝ x' *fraction-ℤ y'
ap-mul-fraction-ℤ p q = ap-binary mul-fraction-ℤ p q
```

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
      by helper {nx} {ny} {dx'} {dy'}
    ＝ (nx' *ℤ dx) *ℤ (ny' *ℤ dy)
      by ap-mul-ℤ  p q
    ＝ (nx' *ℤ ny') *ℤ (dx *ℤ dy)
      by helper {nx'} {dx} {ny'} {dy} where
      helper : {a b c d : ℤ} → (a *ℤ b) *ℤ (c *ℤ d) ＝ (a *ℤ c) *ℤ (b *ℤ d)
      helper {a} {b} {c} {d} =
        equational-reasoning
          (a *ℤ b) *ℤ (c *ℤ d)
          ＝ a *ℤ (b *ℤ (c *ℤ d))
            by  associative-mul-ℤ  a b (mul-ℤ c d)
          ＝ a *ℤ ((b *ℤ c) *ℤ d)
            by  ap-mul-ℤ (refl {x = a}) (inv (associative-mul-ℤ b c d))
          ＝ a *ℤ ((c *ℤ b) *ℤ d)
            by ap (λ x → a *ℤ (x *ℤ d)) (commutative-mul-ℤ b c)
          ＝ a *ℤ (c *ℤ (b *ℤ d))
            by  ap-mul-ℤ (refl {x = a}) (associative-mul-ℤ c b d)
          ＝ (a *ℤ c) *ℤ (b *ℤ d)
            by  inv (associative-mul-ℤ  a c (mul-ℤ b d))

```

### Unit laws

```agda
left-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ one-fraction-ℤ  k) k
left-unit-law-mul-fraction-ℤ k = refl

right-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ k one-fraction-ℤ) k
right-unit-law-mul-fraction-ℤ (n , d , p) =
  equational-reasoning
    (n *ℤ one-ℤ) *ℤ d
    ＝ n *ℤ d
    by ap-mul-ℤ (right-unit-law-mul-ℤ n) refl
    ＝ n *ℤ (d *ℤ one-ℤ)
    by ap-mul-ℤ {n} refl (inv (right-unit-law-mul-ℤ d))
```

### Multiplication is associative

```agda
associative-add-fraction-ℤ :
  (x y z : fraction-ℤ) →
  sim-fraction-ℤ
    (mul-fraction-ℤ (mul-fraction-ℤ x y) z)
    (mul-fraction-ℤ x (mul-fraction-ℤ y z))
associative-add-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) (nz , dz , dzp) =
  equational-reasoning
  ((nx *ℤ ny) *ℤ nz) *ℤ (dx *ℤ (dy *ℤ dz)) 
  ＝ (nx *ℤ (ny *ℤ nz)) *ℤ ((dx *ℤ dy) *ℤ dz)
  by  ap-mul-ℤ (associative-mul-ℤ nx ny nz) (inv (associative-mul-ℤ dx dy dz))
 ```

### Multiplication is commutative

```agda
commutative-mul-fraction-ℤ :
  (x y : fraction-ℤ) →
  sim-fraction-ℤ
    (x *fraction-ℤ y)
    (y *fraction-ℤ x)
commutative-mul-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) =
  ap-mul-ℤ (commutative-mul-ℤ nx ny) (commutative-mul-ℤ dy dx)
```
