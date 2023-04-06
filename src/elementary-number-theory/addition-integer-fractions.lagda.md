# Addition on integer fractions

```agda
module elementary-number-theory.addition-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.addition-integers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.equality-dependent-pair-types
open import foundation.equality-cartesian-product-types
```

</details>

## Idea

We introduce addition on integer fractions and derive its basic properties. Note
that the properties only hold up to fraction similarity.

## Definition

```agda
add-fraction-ℤ : fraction-ℤ → fraction-ℤ → fraction-ℤ
pr1 (add-fraction-ℤ (m , (n , n-pos)) (m' , (n' , n'-pos))) =
  add-ℤ (mul-ℤ m n') (mul-ℤ m' n)
pr1 (pr2 (add-fraction-ℤ (m , (n , n-pos)) (m' , (n' , n'-pos)))) =
  mul-ℤ n n'
pr2 (pr2 (add-fraction-ℤ (m , (n , n-pos)) (m' , (n' , n'-pos)))) =
  is-positive-mul-ℤ n-pos n'-pos

add-fraction-ℤ' : fraction-ℤ → fraction-ℤ → fraction-ℤ
add-fraction-ℤ' x y = add-fraction-ℤ y x

ap-add-fraction-ℤ :
  {x y x' y' : fraction-ℤ} → x ＝ x' → y ＝ y' →
  add-fraction-ℤ x y ＝ add-fraction-ℤ x' y'
ap-add-fraction-ℤ p q = ap-binary add-fraction-ℤ p q
```

## Properties

### Unit laws

```agda
left-unit-law-add-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (add-fraction-ℤ zero-fraction-ℤ k) k
left-unit-law-add-fraction-ℤ (m , (n , p)) =
  ap-mul-ℤ (right-unit-law-mul-ℤ m) refl

right-unit-law-add-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (add-fraction-ℤ k zero-fraction-ℤ) k
right-unit-law-add-fraction-ℤ (m , (n , p)) =
 ap-mul-ℤ
   ( ap-add-ℤ (right-unit-law-mul-ℤ m) refl ∙ right-unit-law-add-ℤ m )
   ( inv (right-unit-law-mul-ℤ n))
```
