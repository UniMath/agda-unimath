# Addition on integer fractions

```agda
module elementary-number-theory.addition-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

We introduce addition on integer fractions and derive its basic properties. Note
that the properties only hold up to fraction similarity.

## Definition

```agda
add-fraction-ℤ : fraction-ℤ → fraction-ℤ → fraction-ℤ
pr1 (add-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos)) =
  (m *ℤ n') +ℤ (m' *ℤ n)
pr1 (pr2 (add-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) =
  n *ℤ n'
pr2 (pr2 (add-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) =
  is-positive-mul-ℤ n-pos n'-pos

add-fraction-ℤ' : fraction-ℤ → fraction-ℤ → fraction-ℤ
add-fraction-ℤ' x y = add-fraction-ℤ y x

infixl 35 _+fraction-ℤ_
_+fraction-ℤ_ = add-fraction-ℤ

ap-add-fraction-ℤ :
  {x y x' y' : fraction-ℤ} → x ＝ x' → y ＝ y' →
  x +fraction-ℤ y ＝ x' +fraction-ℤ y'
ap-add-fraction-ℤ p q = ap-binary add-fraction-ℤ p q
```

## Properties

### Addition respects the similarity relation

```agda
abstract
  sim-fraction-add-fraction-ℤ :
    {x x' y y' : fraction-ℤ} →
    sim-fraction-ℤ x x' →
    sim-fraction-ℤ y y' →
    sim-fraction-ℤ (x +fraction-ℤ y) (x' +fraction-ℤ y')
  sim-fraction-add-fraction-ℤ
    {(nx , dx , dxp)} {(nx' , dx' , dx'p)}
    {(ny , dy , dyp)} {(ny' , dy' , dy'p)} p q =
    equational-reasoning
      ((nx *ℤ dy) +ℤ (ny *ℤ dx)) *ℤ (dx' *ℤ dy')
      ＝ ((nx *ℤ dy) *ℤ (dx' *ℤ dy')) +ℤ ((ny *ℤ dx) *ℤ (dx' *ℤ dy'))
        by right-distributive-mul-add-ℤ (nx *ℤ dy) (ny *ℤ dx) (dx' *ℤ dy')
      ＝ ((dy *ℤ nx) *ℤ (dx' *ℤ dy')) +ℤ ((dx *ℤ ny) *ℤ (dy' *ℤ dx'))
        by ap-add-ℤ (ap-mul-ℤ (commutative-mul-ℤ nx dy) refl)
          (ap-mul-ℤ (commutative-mul-ℤ ny dx) (commutative-mul-ℤ dx' dy'))
      ＝ (((dy *ℤ nx) *ℤ dx') *ℤ dy') +ℤ (((dx *ℤ ny) *ℤ dy') *ℤ dx')
        by ap-add-ℤ (inv (associative-mul-ℤ (dy *ℤ nx) dx' dy'))
          (inv (associative-mul-ℤ (dx *ℤ ny) dy' dx'))
      ＝ ((dy *ℤ (nx *ℤ dx')) *ℤ dy') +ℤ ((dx *ℤ (ny *ℤ dy')) *ℤ dx')
        by ap-add-ℤ (ap-mul-ℤ (associative-mul-ℤ dy nx dx') refl)
          (ap-mul-ℤ (associative-mul-ℤ dx ny dy') refl)
      ＝ ((dy *ℤ (dx *ℤ nx')) *ℤ dy') +ℤ ((dx *ℤ (dy *ℤ ny')) *ℤ dx')
        by ap-add-ℤ
          (ap-mul-ℤ (ap-mul-ℤ (refl {x = dy}) (p ∙ commutative-mul-ℤ nx' dx))
            (refl {x = dy'}))
          (ap-mul-ℤ (ap-mul-ℤ (refl {x = dx}) (q ∙ commutative-mul-ℤ ny' dy))
            (refl {x = dx'}))
      ＝ (((dy *ℤ dx) *ℤ nx') *ℤ dy') +ℤ (((dx *ℤ dy) *ℤ ny') *ℤ dx')
        by ap-add-ℤ (ap-mul-ℤ (inv (associative-mul-ℤ dy dx nx')) refl)
          (ap-mul-ℤ (inv (associative-mul-ℤ dx dy ny')) refl)
      ＝ ((nx' *ℤ (dy *ℤ dx)) *ℤ dy') +ℤ ((ny' *ℤ (dx *ℤ dy)) *ℤ dx')
        by ap-add-ℤ (ap-mul-ℤ (commutative-mul-ℤ (dy *ℤ dx) nx') refl)
          (ap-mul-ℤ (commutative-mul-ℤ (dx *ℤ dy) ny') refl)
      ＝ (nx' *ℤ ((dy *ℤ dx) *ℤ dy')) +ℤ (ny' *ℤ ((dx *ℤ dy) *ℤ dx'))
        by ap-add-ℤ (associative-mul-ℤ nx' (dy *ℤ dx) dy')
          (associative-mul-ℤ ny' (dx *ℤ dy) dx')
      ＝ (nx' *ℤ (dy' *ℤ (dy *ℤ dx))) +ℤ (ny' *ℤ (dx' *ℤ (dx *ℤ dy)))
        by ap-add-ℤ
          (ap-mul-ℤ (refl {x = nx'}) (commutative-mul-ℤ (dy *ℤ dx) dy'))
          (ap-mul-ℤ (refl {x = ny'}) (commutative-mul-ℤ (dx *ℤ dy) dx'))
      ＝ ((nx' *ℤ dy') *ℤ (dy *ℤ dx)) +ℤ ((ny' *ℤ dx') *ℤ (dx *ℤ dy))
        by ap-add-ℤ (inv (associative-mul-ℤ nx' dy' (dy *ℤ dx)))
          (inv (associative-mul-ℤ ny' dx' (dx *ℤ dy)))
      ＝ ((nx' *ℤ dy') *ℤ (dx *ℤ dy)) +ℤ ((ny' *ℤ dx') *ℤ (dx *ℤ dy))
        by ap-add-ℤ
          (ap-mul-ℤ (refl {x = nx' *ℤ dy'}) (commutative-mul-ℤ dy dx)) refl
      ＝ ((nx' *ℤ dy') +ℤ (ny' *ℤ dx')) *ℤ (dx *ℤ dy)
        by inv (right-distributive-mul-add-ℤ (nx' *ℤ dy') _ (dx *ℤ dy))
```

### Unit laws

```agda
abstract
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
```

### Addition is associative

```agda
abstract
  associative-add-fraction-ℤ :
    (x y z : fraction-ℤ) →
    sim-fraction-ℤ
      ((x +fraction-ℤ y) +fraction-ℤ z)
      (x +fraction-ℤ (y +fraction-ℤ z))
  associative-add-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) (nz , dz , dzp) =
    ap-mul-ℤ (eq-num) (inv (associative-mul-ℤ dx dy dz))
    where
    eq-num :
      ( ((nx *ℤ dy) +ℤ (ny *ℤ dx)) *ℤ dz) +ℤ (nz *ℤ (dx *ℤ dy)) ＝
      ( (nx *ℤ (dy *ℤ dz)) +ℤ (((ny *ℤ dz) +ℤ (nz *ℤ dy)) *ℤ dx))
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
```

### Addition is commutative

```agda
abstract
  commutative-add-fraction-ℤ :
    (x y : fraction-ℤ) →
    sim-fraction-ℤ
      (x +fraction-ℤ y)
      (y +fraction-ℤ x)
  commutative-add-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) =
    ap-mul-ℤ
      ( commutative-add-ℤ (nx *ℤ dy) (ny *ℤ dx))
      ( commutative-mul-ℤ dy dx)
```

### The numerator of the sum of an integer fraction and its negative is zero

```agda
abstract
  is-zero-numerator-add-left-neg-fraction-ℤ :
    (x : fraction-ℤ) →
    is-zero-ℤ (numerator-fraction-ℤ (add-fraction-ℤ (neg-fraction-ℤ x) x))
  is-zero-numerator-add-left-neg-fraction-ℤ (p , q , H) =
    ap (_+ℤ (p *ℤ q)) (left-negative-law-mul-ℤ p q) ∙
    left-inverse-law-add-ℤ (p *ℤ q)

  is-zero-numerator-add-right-neg-fraction-ℤ :
    (x : fraction-ℤ) →
    is-zero-ℤ (numerator-fraction-ℤ (add-fraction-ℤ x (neg-fraction-ℤ x)))
  is-zero-numerator-add-right-neg-fraction-ℤ (p , q , H) =
    ap ((p *ℤ q) +ℤ_) (left-negative-law-mul-ℤ p q) ∙
    right-inverse-law-add-ℤ (p *ℤ q)
```

### Distributivity of negatives over addition on the integer fractions

```agda
abstract
  distributive-neg-add-fraction-ℤ :
    (x y : fraction-ℤ) →
    sim-fraction-ℤ
      ( neg-fraction-ℤ (x +fraction-ℤ y))
      ( neg-fraction-ℤ x +fraction-ℤ neg-fraction-ℤ y)
  distributive-neg-add-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) =
    ap
      ( _*ℤ (dx *ℤ dy))
      ( ( distributive-neg-add-ℤ (nx *ℤ dy) (ny *ℤ dx)) ∙
        ( ap-add-ℤ
          ( inv (left-negative-law-mul-ℤ nx dy))
          ( inv (left-negative-law-mul-ℤ ny dx))))
```

### The inclusion of integers preserves addition

```agda
abstract
  add-in-fraction-ℤ :
    (x y : ℤ) →
    sim-fraction-ℤ
      (in-fraction-ℤ x +fraction-ℤ in-fraction-ℤ y)
      (in-fraction-ℤ (x +ℤ y))
  add-in-fraction-ℤ x y =
    ap-binary
      ( λ a b → (a +ℤ b) *ℤ one-ℤ)
      ( right-unit-law-mul-ℤ x)
      ( right-unit-law-mul-ℤ y)
```
