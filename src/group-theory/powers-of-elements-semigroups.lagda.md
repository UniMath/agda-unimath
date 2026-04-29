# Powers of elements in semigroups

```agda
module group-theory.powers-of-elements-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="semigroup" Agda=power-Semigroup}} on a [semigroup](group-theory.semigroups.md) is the map
`n x ↦ xⁿ`, which is defined by [iteratively](foundation.iterating-functions.md)
multiplying `x` with itself `n` times, where `n` is a [nonzero natural number](elementary-number-theory.positive-natural-numbers.md).

We define the power operation such that the following equalities hold by definition:

```text
  x¹ ≐ x
  xⁿ⁺² ≐ xⁿ⁺¹ · x.
```

## Definitions

### Powers of elements of semigroups

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  power-succ-Semigroup :
    (n : ℕ) → type-Semigroup G → type-Semigroup G
  power-succ-Semigroup zero-ℕ x = x
  power-succ-Semigroup (succ-ℕ n) x =
    mul-Semigroup G (power-succ-Semigroup n x) x 

  power-Semigroup :
    ℕ⁺ → type-Semigroup G → type-Semigroup G
  power-Semigroup (zero-ℕ , H) = ex-falso (H refl)
  power-Semigroup (succ-ℕ n , H) = power-succ-Semigroup n
```

### The predicate of being a power of an element of a semigroup

We say that an element `y` **is a power** of an element `x` if there
[exists](foundation.existential-quantification.md) a number `n` such that
`xⁿ ＝ y`.

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  is-power-of-element-prop-Semigroup : (x y : type-Semigroup G) → Prop l
  is-power-of-element-prop-Semigroup x y =
    exists-structure-Prop ℕ⁺ (λ n → power-Semigroup G n x ＝ y)

  is-power-of-element-Semigroup : (x y : type-Semigroup G) → UU l
  is-power-of-element-Semigroup x y =
    type-Prop (is-power-of-element-prop-Semigroup x y)

  is-prop-is-power-of-element-Semigroup :
    (x y : type-Semigroup G) → is-prop (is-power-of-element-Semigroup x y)
  is-prop-is-power-of-element-Semigroup x y =
    is-prop-type-Prop (is-power-of-element-prop-Semigroup x y)
```

## Properties

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  abstract
    successor-law-power-Semigroup :
      (n : ℕ⁺) (x : type-Semigroup G) →
      power-Semigroup G (succ-ℕ⁺ n) x ＝
      mul-Semigroup G (power-Semigroup G n x) x
    successor-law-power-Semigroup (zero-ℕ , H) x = ex-falso (H refl)
    successor-law-power-Semigroup (succ-ℕ n , H) x = refl
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  abstract
    successor-law-power-succ-Semigroup' :
      (n : ℕ) (x : type-Semigroup G) →
      power-succ-Semigroup G (succ-ℕ n) x ＝
      mul-Semigroup G x (power-succ-Semigroup G n x)
    successor-law-power-succ-Semigroup' zero-ℕ x = refl
    successor-law-power-succ-Semigroup' (succ-ℕ n) x =
      ap (mul-Semigroup' G x) (successor-law-power-succ-Semigroup' n x) ∙
      associative-mul-Semigroup G x (power-succ-Semigroup G n x) x
  
    successor-law-power-Semigroup' :
      (n : ℕ⁺) (x : type-Semigroup G) →
      power-Semigroup G (succ-ℕ⁺ n) x ＝
      mul-Semigroup G x (power-Semigroup G n x)
    successor-law-power-Semigroup' (zero-ℕ , H) x =
      ex-falso (H refl)
    successor-law-power-Semigroup' (succ-ℕ n , H) x =
      successor-law-power-succ-Semigroup' n x
```

### Powers by sums of nonnegative natural numbers are products of powers

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  abstract
    distributive-power-succ-add-Semigroup :
      (m : ℕ⁺) (n : ℕ) {x : type-Semigroup G} →
      power-succ-Semigroup G (nat-ℕ⁺ m +ℕ n) x ＝
      mul-Semigroup G (power-Semigroup G m x) (power-succ-Semigroup G n x)
    distributive-power-succ-add-Semigroup (zero-ℕ , H) zero-ℕ =
      ex-falso (H refl)
    distributive-power-succ-add-Semigroup (succ-ℕ m , H) zero-ℕ =
      refl
    distributive-power-succ-add-Semigroup (zero-ℕ , H) (succ-ℕ n) =
      ex-falso (H refl)
    distributive-power-succ-add-Semigroup (succ-ℕ m , H) (succ-ℕ n) =
      ap
        ( mul-Semigroup' G _)
        ( distributive-power-succ-add-Semigroup (succ-ℕ m , H) n) ∙
      associative-mul-Semigroup G _ _ _

    distributive-power-add-Semigroup :
      (m n : ℕ⁺) {x : type-Semigroup G} →
      power-Semigroup G (m +ℕ⁺ n) x ＝
      mul-Semigroup G (power-Semigroup G m x) (power-Semigroup G n x)
    distributive-power-add-Semigroup m (zero-ℕ , K) = ex-falso (K refl)
    distributive-power-add-Semigroup m (succ-ℕ n , K) =
      distributive-power-succ-add-Semigroup m n
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  abstract
    commute-power-succ-Semigroup' :
      (n : ℕ) {x y : type-Semigroup G} →
      mul-Semigroup G x y ＝ mul-Semigroup G y x →
      mul-Semigroup G (power-succ-Semigroup G n x) y ＝
      mul-Semigroup G y (power-succ-Semigroup G n x)
    commute-power-succ-Semigroup' zero-ℕ p = p
    commute-power-succ-Semigroup' (succ-ℕ n) p =
      right-swap-mul-Semigroup G p ∙
      associative-mul-Semigroup G _ _ _ ∙
      left-swap-mul-Semigroup G (commute-power-succ-Semigroup' n p)

    commute-powers-Semigroup' :
      (n : ℕ⁺) {x y : type-Semigroup G} →
      mul-Semigroup G x y ＝ mul-Semigroup G y x →
      mul-Semigroup G (power-Semigroup G n x) y ＝
      mul-Semigroup G y (power-Semigroup G n x)
    commute-powers-Semigroup' (zero-ℕ , H) = ex-falso (H refl)
    commute-powers-Semigroup' (succ-ℕ n , H) = commute-power-succ-Semigroup' n

    commute-powers-Semigroup :
      (m n : ℕ⁺) {x y : type-Semigroup G} →
      mul-Semigroup G x y ＝ mul-Semigroup G y x →
      mul-Semigroup G (power-Semigroup G m x) (power-Semigroup G n y) ＝
      mul-Semigroup G (power-Semigroup G n y) (power-Semigroup G m x)
    commute-powers-Semigroup m n p =
      inv (commute-powers-Semigroup' n (inv (commute-powers-Semigroup' m p)))
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  abstract
    distributive-power-succ-mul-Semigroup :
      (n : ℕ) {x y : type-Semigroup G} →
      mul-Semigroup G x y ＝ mul-Semigroup G y x →
      power-succ-Semigroup G n (mul-Semigroup G x y) ＝
      mul-Semigroup G (power-succ-Semigroup G n x) (power-succ-Semigroup G n y)
    distributive-power-succ-mul-Semigroup zero-ℕ p = refl
    distributive-power-succ-mul-Semigroup (succ-ℕ n) p =
      ap (mul-Semigroup' G _) (distributive-power-succ-mul-Semigroup n p) ∙
      interchange-mul-mul-Semigroup G
        ( commute-power-succ-Semigroup' G n (inv p))

    distributive-power-mul-Semigroup :
      (n : ℕ⁺) {x y : type-Semigroup G} →
      mul-Semigroup G x y ＝ mul-Semigroup G y x →
      power-Semigroup G n (mul-Semigroup G x y) ＝
      mul-Semigroup G (power-Semigroup G n x) (power-Semigroup G n y)
    distributive-power-mul-Semigroup (zero-ℕ , H) p = ex-falso (H refl)
    distributive-power-mul-Semigroup (succ-ℕ n , H) p =
      distributive-power-succ-mul-Semigroup n p
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  abstract
    power-succ-mul-Semigroup :
      (m n : ℕ) {x : type-Semigroup G} →
      power-succ-Semigroup G (m *ℕ (n +ℕ 1) +ℕ n) x ＝
      power-succ-Semigroup G n (power-succ-Semigroup G m x)
    power-succ-mul-Semigroup zero-ℕ n =
      ap
        ( λ t → power-succ-Semigroup G t _)
        ( ap (add-ℕ' n) (left-zero-law-mul-ℕ (n +ℕ 1)) ∙ left-unit-law-add-ℕ n)
    power-succ-mul-Semigroup (succ-ℕ m) n =
      distributive-power-succ-add-Semigroup G
        ( nonzero-succ-ℕ m *ℕ⁺ nonzero-succ-ℕ n)
        ( n) ∙
      ap (mul-Semigroup' G _) (power-succ-mul-Semigroup m n) ∙
      inv
        ( distributive-power-succ-mul-Semigroup G n
          ( successor-law-power-succ-Semigroup' G m _))

    power-mul-Semigroup :
      (m n : ℕ⁺) {x : type-Semigroup G} →
      power-Semigroup G (m *ℕ⁺ n) x ＝
      power-Semigroup G n (power-Semigroup G m x)
    power-mul-Semigroup (zero-ℕ , H) n = ex-falso (H refl)
    power-mul-Semigroup (succ-ℕ m , H) (zero-ℕ , K) = ex-falso (K refl)
    power-mul-Semigroup (succ-ℕ m , H) (succ-ℕ n , K) =
      power-succ-mul-Semigroup m n
```

### Semigroup homomorphisms preserve powers

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : hom-Semigroup G H)
  where

  abstract
    preserves-power-succ-hom-Semigroup :
      (n : ℕ) {x : type-Semigroup G} →
      map-hom-Semigroup G H f (power-succ-Semigroup G n x) ＝
      power-succ-Semigroup H n (map-hom-Semigroup G H f x)
    preserves-power-succ-hom-Semigroup zero-ℕ = refl
    preserves-power-succ-hom-Semigroup (succ-ℕ n) =
      preserves-mul-hom-Semigroup G H f ∙
      ap (mul-Semigroup' H _) (preserves-power-succ-hom-Semigroup n)

    preserves-power-hom-Semigroup :
      (n : ℕ⁺) {x : type-Semigroup G} →
      map-hom-Semigroup G H f (power-Semigroup G n x) ＝
      power-Semigroup H n (map-hom-Semigroup G H f x)
    preserves-power-hom-Semigroup (zero-ℕ , H) = ex-falso (H refl)
    preserves-power-hom-Semigroup (succ-ℕ n , H) =
      preserves-power-succ-hom-Semigroup n
```
