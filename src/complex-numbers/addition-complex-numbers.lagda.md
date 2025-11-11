# Addition of complex numbers

```agda
module complex-numbers.addition-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
```

</details>

## Idea

We introduce {{#concept "addition" Disambiguation="complex numbers" Agda=add-ℂ}}
on the [complex numbers](complex-numbers.complex-numbers.md) by componentwise
[addition](real-numbers.addition-real-numbers.md) of the
[real](real-numbers.dedekind-real-numbers.md) and imaginary parts.

## Definition

```agda
add-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → ℂ (l1 ⊔ l2)
add-ℂ (a , b) (c , d) = (a +ℝ c , b +ℝ d)

infixl 35 _+ℂ_
_+ℂ_ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → ℂ (l1 ⊔ l2)
_+ℂ_ = add-ℂ

ap-add-ℂ :
  {l1 l2 : Level} →
  {x x' : ℂ l1} → x ＝ x' → {y y' : ℂ l2} → y ＝ y' →
  x +ℂ y ＝ x' +ℂ y'
ap-add-ℂ = ap-binary add-ℂ
```

## Properties

### Addition is commutative

```agda
abstract
  commutative-add-ℂ : {l1 l2 : Level} (x : ℂ l1) (y : ℂ l2) → x +ℂ y ＝ y +ℂ x
  commutative-add-ℂ _ _ = eq-ℂ (commutative-add-ℝ _ _) (commutative-add-ℝ _ _)
```

### Addition is associative

```agda
abstract
  associative-add-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    (x +ℂ y) +ℂ z ＝ x +ℂ (y +ℂ z)
  associative-add-ℂ _ _ _ =
    eq-ℂ (associative-add-ℝ _ _ _) (associative-add-ℝ _ _ _)
```

### Unit laws of addition

```agda
abstract
  left-unit-law-add-ℂ : {l : Level} (x : ℂ l) → zero-ℂ +ℂ x ＝ x
  left-unit-law-add-ℂ (a , b) =
    eq-ℂ (left-unit-law-add-ℝ a) (left-unit-law-add-ℝ b)

  right-unit-law-add-ℂ : {l : Level} (x : ℂ l) → x +ℂ zero-ℂ ＝ x
  right-unit-law-add-ℂ (a , b) =
    eq-ℂ (right-unit-law-add-ℝ a) (right-unit-law-add-ℝ b)
```

### Inverse laws of addition

```agda
abstract
  left-inverse-law-add-ℂ : {l : Level} (x : ℂ l) → sim-ℂ (neg-ℂ x +ℂ x) zero-ℂ
  left-inverse-law-add-ℂ (a , b) =
    ( left-inverse-law-add-ℝ a , left-inverse-law-add-ℝ b)

  right-inverse-law-add-ℂ :
    {l : Level} (x : ℂ l) → sim-ℂ (x +ℂ neg-ℂ x) zero-ℂ
  right-inverse-law-add-ℂ (a , b) =
    ( right-inverse-law-add-ℝ a , right-inverse-law-add-ℝ b)
```

### Similarity is preserved by addition

```agda
abstract
  preserves-sim-add-ℂ :
    {l1 l2 l3 l4 : Level} {x : ℂ l1} {x' : ℂ l2} {y : ℂ l3} {y' : ℂ l4} →
    sim-ℂ x x' → sim-ℂ y y' → sim-ℂ (x +ℂ y) (x' +ℂ y')
  preserves-sim-add-ℂ (a~a' , b~b') (c~c' , d~d') =
    ( preserves-sim-add-ℝ a~a' c~c' , preserves-sim-add-ℝ b~b' d~d')
```
