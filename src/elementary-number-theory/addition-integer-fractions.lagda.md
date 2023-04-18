# Addition on integer fractions

```agda
module elementary-number-theory.addition-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integers

open import foundation.dependent-pair-types
open import foundation.equational-reasoning
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
  add-ℤ (mul-ℤ m n') (mul-ℤ m' n)
pr1 (pr2 (add-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) =
  mul-ℤ n n'
pr2 (pr2 (add-fraction-ℤ (m , n , n-pos) (m' , n' , n'-pos))) =
  is-positive-mul-ℤ n-pos n'-pos

add-fraction-ℤ' : fraction-ℤ → fraction-ℤ → fraction-ℤ
add-fraction-ℤ' x y = add-fraction-ℤ y x

infix 30 _+fraction-ℤ_
_+fraction-ℤ_ = add-fraction-ℤ

ap-add-fraction-ℤ :
  {x y x' y' : fraction-ℤ} → x ＝ x' → y ＝ y' →
  x +fraction-ℤ y ＝ x' +fraction-ℤ y'
ap-add-fraction-ℤ p q = ap-binary add-fraction-ℤ p q
```

## Properties

### Addition respects the similarity relation

```agda
sim-fraction-add-fraction-ℤ :
  {x x' y y' : fraction-ℤ} →
  sim-fraction-ℤ x x' →
  sim-fraction-ℤ y y' →
  sim-fraction-ℤ (x +fraction-ℤ y) (x' +fraction-ℤ y')
sim-fraction-add-fraction-ℤ
  {(nx , dx , dxp)} {(nx' , dx' , dx'p)}
  {(ny , dy , dyp)} {(ny' , dy' , dy'p)} p q =
  equational-reasoning
  mul-ℤ ((mul-ℤ nx dy) +ℤ (mul-ℤ ny dx)) (mul-ℤ dx' dy')
  ＝ mul-ℤ (mul-ℤ nx dy) (mul-ℤ dx' dy') +ℤ mul-ℤ (mul-ℤ ny dx) (mul-ℤ dx' dy')
    by right-distributive-mul-add-ℤ (mul-ℤ nx dy) (mul-ℤ ny dx) (mul-ℤ dx' dy')
  ＝ mul-ℤ (mul-ℤ dy nx) (mul-ℤ dx' dy') +ℤ mul-ℤ (mul-ℤ dx ny) (mul-ℤ dy' dx')
    by ap-add-ℤ (ap-mul-ℤ (commutative-mul-ℤ nx dy) refl)
      (ap-mul-ℤ (commutative-mul-ℤ ny dx) (commutative-mul-ℤ dx' dy'))
  ＝ mul-ℤ (mul-ℤ (mul-ℤ dy nx) dx') dy' +ℤ mul-ℤ (mul-ℤ (mul-ℤ dx ny) dy') dx'
    by ap-add-ℤ (inv (associative-mul-ℤ (mul-ℤ dy nx) dx' dy'))
      (inv (associative-mul-ℤ (mul-ℤ dx ny) dy' dx'))
  ＝ mul-ℤ (mul-ℤ dy (mul-ℤ nx dx')) dy' +ℤ mul-ℤ (mul-ℤ dx (mul-ℤ ny dy')) dx'
    by ap-add-ℤ (ap-mul-ℤ (associative-mul-ℤ dy nx dx') refl)
      (ap-mul-ℤ (associative-mul-ℤ dx ny dy') refl)
  ＝ mul-ℤ (mul-ℤ dy (mul-ℤ dx nx')) dy' +ℤ mul-ℤ (mul-ℤ dx (mul-ℤ dy ny')) dx'
    by ap-add-ℤ
      (ap-mul-ℤ (ap-mul-ℤ (refl {x = dy}) (p ∙ commutative-mul-ℤ nx' dx))
        (refl {x = dy'}))
      (ap-mul-ℤ (ap-mul-ℤ (refl {x = dx}) (q ∙ commutative-mul-ℤ ny' dy))
        (refl {x = dx'}))
  ＝ mul-ℤ (mul-ℤ (mul-ℤ dy dx) nx') dy' +ℤ mul-ℤ (mul-ℤ (mul-ℤ dx dy) ny') dx'
    by ap-add-ℤ (ap-mul-ℤ (inv (associative-mul-ℤ dy dx nx')) refl)
      (ap-mul-ℤ (inv (associative-mul-ℤ dx dy ny')) refl)
  ＝ mul-ℤ (mul-ℤ nx' (mul-ℤ dy dx)) dy' +ℤ mul-ℤ (mul-ℤ ny' (mul-ℤ dx dy)) dx'
    by ap-add-ℤ (ap-mul-ℤ (commutative-mul-ℤ (mul-ℤ dy dx) nx') refl)
      (ap-mul-ℤ (commutative-mul-ℤ (mul-ℤ dx dy) ny') refl)
  ＝ mul-ℤ nx' (mul-ℤ (mul-ℤ dy dx) dy') +ℤ mul-ℤ ny' (mul-ℤ (mul-ℤ dx dy) dx')
    by ap-add-ℤ (associative-mul-ℤ nx' (mul-ℤ dy dx) dy')
      (associative-mul-ℤ ny' (mul-ℤ dx dy) dx')
  ＝ mul-ℤ nx' (mul-ℤ dy' (mul-ℤ dy dx)) +ℤ mul-ℤ ny' (mul-ℤ dx' (mul-ℤ dx dy))
    by ap-add-ℤ (ap-mul-ℤ (refl {x = nx'}) (commutative-mul-ℤ (mul-ℤ dy dx) dy'))
      (ap-mul-ℤ (refl {x = ny'}) (commutative-mul-ℤ (mul-ℤ dx dy) dx'))
  ＝ mul-ℤ (mul-ℤ nx' dy') (mul-ℤ dy dx) +ℤ mul-ℤ (mul-ℤ ny' dx') (mul-ℤ dx dy)
    by ap-add-ℤ (inv (associative-mul-ℤ nx' dy' (mul-ℤ dy dx)))
      (inv (associative-mul-ℤ ny' dx' (mul-ℤ dx dy)))
  ＝ mul-ℤ (mul-ℤ nx' dy') (mul-ℤ dx dy) +ℤ mul-ℤ (mul-ℤ ny' dx') (mul-ℤ dx dy)
    by ap-add-ℤ
      (ap-mul-ℤ (refl {x = mul-ℤ nx' dy'}) (commutative-mul-ℤ dy dx)) refl
  ＝ mul-ℤ ((mul-ℤ nx' dy') +ℤ (mul-ℤ ny' dx')) (mul-ℤ dx dy)
    by inv (right-distributive-mul-add-ℤ (mul-ℤ nx' dy') _ (mul-ℤ dx dy))
```

### Unit laws

```agda
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
   ( ap-add-ℤ (right-unit-law-mul-ℤ m) refl ∙ right-unit-law-add-ℤ m )
   ( inv (right-unit-law-mul-ℤ n))
```

### Addition is associative

```agda
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
      mul-ℤ ((mul-ℤ nx dy) +ℤ (mul-ℤ ny dx)) dz +ℤ mul-ℤ nz (mul-ℤ dx dy) ＝
      mul-ℤ nx (mul-ℤ dy dz) +ℤ (mul-ℤ (mul-ℤ ny dz +ℤ mul-ℤ nz dy) dx)
    eq-num = equational-reasoning
      mul-ℤ ((mul-ℤ nx dy) +ℤ (mul-ℤ ny dx)) dz +ℤ mul-ℤ nz (mul-ℤ dx dy)
      ＝ (mul-ℤ (mul-ℤ nx dy) dz +ℤ mul-ℤ (mul-ℤ ny dx) dz) +ℤ
          mul-ℤ nz (mul-ℤ dx dy)
        by ap-add-ℤ
          (right-distributive-mul-add-ℤ (mul-ℤ nx dy) (mul-ℤ ny dx) dz) refl
      ＝ mul-ℤ (mul-ℤ nx dy) dz +ℤ
          (mul-ℤ (mul-ℤ ny dx) dz +ℤ mul-ℤ nz (mul-ℤ dx dy))
        by associative-add-ℤ
          (mul-ℤ (mul-ℤ nx dy) dz) (mul-ℤ (mul-ℤ ny dx) dz) _
      ＝ mul-ℤ nx (mul-ℤ dy dz) +ℤ
          (mul-ℤ (mul-ℤ ny dx) dz +ℤ mul-ℤ nz (mul-ℤ dx dy))
        by ap-add-ℤ (associative-mul-ℤ nx dy dz) refl
      ＝ mul-ℤ nx (mul-ℤ dy dz) +ℤ
          (mul-ℤ ny (mul-ℤ dz dx) +ℤ mul-ℤ nz (mul-ℤ dy dx))
        by ap-add-ℤ
          (refl {x = mul-ℤ nx (mul-ℤ dy dz)})
          (ap-add-ℤ
            (associative-mul-ℤ ny dx dz ∙ ap-mul-ℤ (refl {x = ny})
              (commutative-mul-ℤ dx dz))
            (ap-mul-ℤ (refl {x = nz}) (commutative-mul-ℤ dx dy)))
      ＝ mul-ℤ nx (mul-ℤ dy dz) +ℤ
          (mul-ℤ (mul-ℤ ny dz) dx +ℤ mul-ℤ (mul-ℤ nz dy) dx)
        by ap-add-ℤ
          (refl {x = mul-ℤ nx (mul-ℤ dy dz)})
          (inv (ap-add-ℤ (associative-mul-ℤ ny dz dx) (associative-mul-ℤ nz dy dx)))
      ＝ mul-ℤ nx (mul-ℤ dy dz) +ℤ (mul-ℤ (mul-ℤ ny dz +ℤ mul-ℤ nz dy) dx)
        by ap-add-ℤ
          (refl {x = mul-ℤ nx (mul-ℤ dy dz)})
          (inv (right-distributive-mul-add-ℤ (mul-ℤ ny dz) (mul-ℤ nz dy) dx))
```

### Addition is commutative

```agda
commutative-add-fraction-ℤ :
  (x y : fraction-ℤ) →
  sim-fraction-ℤ
    (x +fraction-ℤ y)
    (y +fraction-ℤ x)
commutative-add-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) =
  ap-mul-ℤ
    ( commutative-add-ℤ (mul-ℤ nx dy) (mul-ℤ ny dx))
    ( commutative-mul-ℤ dy dx)
```
