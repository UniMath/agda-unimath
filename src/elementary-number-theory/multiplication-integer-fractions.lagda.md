# Addition on integer fractions

```agda
module elementary-number-theory.multiplication-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integers

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
    ＝ nx *ℤ (ny *ℤ (dx' *ℤ dy'))
      by  associative-mul-ℤ  nx ny (mul-ℤ dx' dy')
    ＝ nx *ℤ ((ny *ℤ dx') *ℤ dy')
      by  ap-mul-ℤ (refl {x = nx}) (inv (associative-mul-ℤ ny dx' dy'))
    ＝ nx *ℤ ((dx' *ℤ ny) *ℤ dy')
      by ap (λ x → nx *ℤ (x *ℤ dy')) (commutative-mul-ℤ ny dx')
    ＝ nx *ℤ (dx' *ℤ (ny *ℤ dy'))
      by  ap-mul-ℤ (refl {x = nx}) (associative-mul-ℤ dx' ny dy')
    ＝ (nx *ℤ dx') *ℤ (ny *ℤ dy')
      by  inv (associative-mul-ℤ  nx dx' (mul-ℤ ny dy'))
    ＝ (nx' *ℤ dx) *ℤ (ny' *ℤ dy)
      by ap-mul-ℤ  p q
    ＝ (nx' *ℤ ny') *ℤ (dx *ℤ dy)
      by {!!}
{-
  equational-reasoning
    =
      by ?
-}
```

### Unit laws

```agda
{-
left-unit-law-add-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (zero-fraction-ℤ +fraction-ℤ k) k
left-unit-law-add-fraction-ℤ (m , n , p) =
  ap-mul-ℤ (right-unit-law-mul-ℤ m) refl

right-unit-law-add-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (k +fraction-ℤ zero-fraction-ℤ) k
right-unit-law-add-fraction-ℤ (m , n , p) =
 ap-mul-ℤ
   ( ap-add-ℤ (right-unit-law-mul-ℤ m) refl ∙ right-unit-law-add-ℤ m)
   ( inv (right-unit-law-mul-ℤ n))
-}
```

### Addition is associative

```agda
{-
associative-add-fraction-ℤ :
  (x y z : fraction-ℤ) →
  sim-fraction-ℤ
    ((x +fraction-ℤ y) +fraction-ℤ z)
    (x +fraction-ℤ (y +fraction-ℤ z))
associative-add-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) (nz , dz , dzp) =
  ap-mul-ℤ
    eq-num
    (inv (associative-mul-ℤ dx dy dz))
  where
    eq-num :
      (((nx *ℤ dy) +ℤ (ny *ℤ dx)) *ℤ dz) +ℤ (nz *ℤ (dx *ℤ dy)) ＝
      (nx *ℤ (dy *ℤ dz)) +ℤ (((ny *ℤ dz) +ℤ (nz *ℤ dy)) *ℤ dx)
    eq-num =
      equational-reasoning
        (((nx *ℤ dy) +ℤ (ny *ℤ dx)) *ℤ dz) +ℤ (nz *ℤ (dx *ℤ dy))
        ＝ (((nx *ℤ dy) *ℤ dz) +ℤ ((ny *ℤ dx) *ℤ dz)) +ℤ
            (nz *ℤ (dx *ℤ dy))
          by ap-add-ℤ
            (right-distributive-mul-add-ℤ (nx *ℤ dy) (ny *ℤ dx) dz) refl
        ＝ ((nx *ℤ dy) *ℤ dz) +ℤ
            (((ny *ℤ dx) *ℤ dz) +ℤ (nz *ℤ (dx *ℤ dy)))
          by associative-add-ℤ
            ((nx *ℤ dy) *ℤ dz) ((ny *ℤ dx) *ℤ dz) _
        ＝ (nx *ℤ (dy *ℤ dz)) +ℤ
            (((ny *ℤ dx) *ℤ dz) +ℤ (nz *ℤ (dx *ℤ dy)))
          by ap-add-ℤ (associative-mul-ℤ nx dy dz) refl
        ＝ (nx *ℤ (dy *ℤ dz)) +ℤ
            ((ny *ℤ (dz *ℤ dx)) +ℤ (nz *ℤ (dy *ℤ dx)))
          by ap-add-ℤ
            (refl {x = nx *ℤ (dy *ℤ dz)})
            (ap-add-ℤ
              (associative-mul-ℤ ny dx dz ∙ ap-mul-ℤ (refl {x = ny})
                (commutative-mul-ℤ dx dz))
              (ap-mul-ℤ (refl {x = nz}) (commutative-mul-ℤ dx dy)))
        ＝ (nx *ℤ (dy *ℤ dz)) +ℤ
            (((ny *ℤ dz) *ℤ dx) +ℤ ((nz *ℤ dy) *ℤ dx))
          by ap-add-ℤ
            (refl {x = nx *ℤ (dy *ℤ dz)})
            (inv
              (ap-add-ℤ
                ( associative-mul-ℤ ny dz dx)
                ( associative-mul-ℤ nz dy dx)))
        ＝ (nx *ℤ (dy *ℤ dz)) +ℤ (((ny *ℤ dz) +ℤ (nz *ℤ dy)) *ℤ dx)
          by ap-add-ℤ
            (refl {x = nx *ℤ (dy *ℤ dz)})
            (inv (right-distributive-mul-add-ℤ (ny *ℤ dz) (nz *ℤ dy) dx))
-}
```

### Addition is commutative

```agda
{-
commutative-add-fraction-ℤ :
  (x y : fraction-ℤ) →
  sim-fraction-ℤ
    (x +fraction-ℤ y)
    (y +fraction-ℤ x)
commutative-add-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) =
  ap-mul-ℤ
    ( commutative-add-ℤ (nx *ℤ dy) (ny *ℤ dx))
    ( commutative-mul-ℤ dy dx)
-}
```

