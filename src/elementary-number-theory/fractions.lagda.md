# Fractions

```agda
module elementary-number-theory.fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The type of fractions is the type of pairs `n/m` consisting of an integer `n` and a positive integer `m`. The type of rational numbers is a retract of the type of fractions.

## Definitions

### The type of fractions

```agda
fraction-ℤ : UU lzero
fraction-ℤ = ℤ × positive-ℤ
```

### The numerator of a fraction

```agda
numerator-fraction-ℤ : fraction-ℤ → ℤ
numerator-fraction-ℤ x = pr1 x
```

### The denominator of a fraction

```agda
positive-denominator-fraction-ℤ : fraction-ℤ → positive-ℤ
positive-denominator-fraction-ℤ x = pr2 x

denominator-fraction-ℤ : fraction-ℤ → ℤ
denominator-fraction-ℤ x = pr1 (positive-denominator-fraction-ℤ x)

is-positive-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-positive-ℤ (denominator-fraction-ℤ x)
is-positive-denominator-fraction-ℤ x = pr2 (positive-denominator-fraction-ℤ x)
```

## Properties

### Denominators are nonzero

```agda
is-nonzero-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-nonzero-ℤ (denominator-fraction-ℤ x)
is-nonzero-denominator-fraction-ℤ x =
  is-nonzero-is-positive-ℤ
    ( denominator-fraction-ℤ x)
    ( is-positive-denominator-fraction-ℤ x)
```

### The type of fractions is a set

```agda
is-set-fraction-ℤ : is-set fraction-ℤ
is-set-fraction-ℤ = is-set-Σ is-set-ℤ λ _ → is-set-positive-ℤ
```

```agda
sim-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
sim-fraction-ℤ-Prop x y =
  Id-Prop ℤ-Set
    (mul-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ y))
    (mul-ℤ (numerator-fraction-ℤ y) (denominator-fraction-ℤ x))

sim-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
sim-fraction-ℤ x y = type-Prop (sim-fraction-ℤ-Prop x y)

is-prop-sim-fraction-ℤ : (x y : fraction-ℤ) → is-prop (sim-fraction-ℤ x y)
is-prop-sim-fraction-ℤ x y = is-prop-type-Prop (sim-fraction-ℤ-Prop x y)

refl-sim-fraction-ℤ : (x : fraction-ℤ) → sim-fraction-ℤ x x
refl-sim-fraction-ℤ x = refl

symm-sim-fraction-ℤ : (x y : fraction-ℤ) → sim-fraction-ℤ x y → sim-fraction-ℤ y x
symm-sim-fraction-ℤ x y r = inv r

trans-sim-fraction-ℤ :
  (x y z : fraction-ℤ) → sim-fraction-ℤ x y → sim-fraction-ℤ y z → sim-fraction-ℤ x z
trans-sim-fraction-ℤ x y z r s =
  is-injective-mul-ℤ'
    ( denominator-fraction-ℤ y)
    ( is-nonzero-denominator-fraction-ℤ y)
    ( ( associative-mul-ℤ
        ( numerator-fraction-ℤ x)
        ( denominator-fraction-ℤ z)
        ( denominator-fraction-ℤ y)) ∙
      ( ( ap
          ( mul-ℤ (numerator-fraction-ℤ x))
          ( commutative-mul-ℤ
            ( denominator-fraction-ℤ z)
            ( denominator-fraction-ℤ y))) ∙
        ( ( inv
            ( associative-mul-ℤ
              ( numerator-fraction-ℤ x)
              ( denominator-fraction-ℤ y)
              ( denominator-fraction-ℤ z))) ∙
          ( ( ap ( mul-ℤ' (denominator-fraction-ℤ z)) r) ∙
            ( ( associative-mul-ℤ
                ( numerator-fraction-ℤ y)
                ( denominator-fraction-ℤ x)
                ( denominator-fraction-ℤ z)) ∙
              ( ( ap
                  ( mul-ℤ (numerator-fraction-ℤ y))
                  ( commutative-mul-ℤ
                    ( denominator-fraction-ℤ x)
                    ( denominator-fraction-ℤ z))) ∙
                ( ( inv
                    ( associative-mul-ℤ
                      ( numerator-fraction-ℤ y)
                      ( denominator-fraction-ℤ z)
                      ( denominator-fraction-ℤ x))) ∙
                  ( ( ap (mul-ℤ' (denominator-fraction-ℤ x)) s) ∙
                    ( ( associative-mul-ℤ
                        ( numerator-fraction-ℤ z)
                        ( denominator-fraction-ℤ y)
                        ( denominator-fraction-ℤ x)) ∙
                      ( ( ap
                          ( mul-ℤ (numerator-fraction-ℤ z))
                          ( commutative-mul-ℤ
                            ( denominator-fraction-ℤ y)
                            ( denominator-fraction-ℤ x))) ∙
                        ( inv
                          ( associative-mul-ℤ
                            ( numerator-fraction-ℤ z)
                            ( denominator-fraction-ℤ x)
                            ( denominator-fraction-ℤ y)))))))))))))

eq-rel-sim-fraction-ℤ : Eq-Rel lzero fraction-ℤ
eq-rel-sim-fraction-ℤ = pair (sim-fraction-ℤ-Prop)
  ( pair' (λ {x} → refl-sim-fraction-ℤ x)
    ( pair' (λ {x y} → symm-sim-fraction-ℤ x y)
      (λ {x y z} → trans-sim-fraction-ℤ x y z)))

```
