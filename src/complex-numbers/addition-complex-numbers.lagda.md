# Addition of complex numbers

```agda
module complex-numbers.addition-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
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

### Adding raised complex numbers

```agda
abstract
  add-raise-ℂ :
    {l1 l2 : Level} {z : ℂ l1} {w : ℂ l2} (l3 l4 : Level) →
    raise-ℂ l3 z +ℂ raise-ℂ l4 w ＝ raise-ℂ (l3 ⊔ l4) (z +ℂ w)
  add-raise-ℂ {_} {_} {z} {w} l3 l4 =
    eq-sim-ℂ
      ( transitive-sim-ℂ _ _ _
        ( sim-raise-ℂ (l3 ⊔ l4) (z +ℂ w))
        ( preserves-sim-add-ℂ (sim-raise-ℂ' l3 z) (sim-raise-ℂ' l4 w)))
```

### The sum of `z` and `conjugate-ℂ z` is double `re-ℂ z`

```agda
abstract
  right-add-conjugate-ℂ :
    {l : Level} (z : ℂ l) → z +ℂ conjugate-ℂ z ＝ complex-ℝ (re-ℂ z +ℝ re-ℂ z)
  right-add-conjugate-ℂ (a +iℂ b) = eq-ℂ refl (eq-right-inverse-law-add-ℝ b)
```

### Swapping laws for addition on complex numbers

```agda
module _
  {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3)
  where

  abstract
    right-swap-add-ℂ :
      (x +ℂ y) +ℂ z ＝ (x +ℂ z) +ℂ y
    right-swap-add-ℂ =
      equational-reasoning
        (x +ℂ y) +ℂ z
        ＝ x +ℂ (y +ℂ z) by associative-add-ℂ x y z
        ＝ x +ℂ (z +ℂ y) by ap (x +ℂ_) (commutative-add-ℂ y z)
        ＝ (x +ℂ z) +ℂ y by inv (associative-add-ℂ x z y)

    left-swap-add-ℂ :
      x +ℂ (y +ℂ z) ＝ y +ℂ (x +ℂ z)
    left-swap-add-ℂ =
      equational-reasoning
        x +ℂ (y +ℂ z)
        ＝ (x +ℂ y) +ℂ z by inv (associative-add-ℂ x y z)
        ＝ (y +ℂ x) +ℂ z by ap (_+ℂ z) (commutative-add-ℂ x y)
        ＝ y +ℂ (x +ℂ z) by associative-add-ℂ y x z
```

### Interchange laws for addition on complex numbers

```agda
module _
  {l1 l2 l3 l4 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) (w : ℂ l4)
  where

  abstract
    interchange-law-add-add-ℂ : (x +ℂ y) +ℂ (z +ℂ w) ＝ (x +ℂ z) +ℂ (y +ℂ w)
    interchange-law-add-add-ℂ =
      equational-reasoning
        (x +ℂ y) +ℂ (z +ℂ w)
        ＝ x +ℂ (y +ℂ (z +ℂ w)) by associative-add-ℂ _ _ _
        ＝ x +ℂ (z +ℂ (y +ℂ w)) by ap (x +ℂ_) (left-swap-add-ℂ y z w)
        ＝ (x +ℂ z) +ℂ (y +ℂ w) by inv (associative-add-ℂ x z (y +ℂ w))
```
