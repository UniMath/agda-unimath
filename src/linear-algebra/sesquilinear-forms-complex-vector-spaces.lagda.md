# Sesquilinear forms in complex vector spaces

```agda
module linear-algebra.sesquilinear-forms-complex-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.multiplication-complex-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.complex-vector-spaces
```

</details>

## Idea

A map `f` taking two elements of a
[complex vector space](linear-algebra.complex-vector-spaces.md) is a
{{#concept "sesquilinear form" WDID=Q1931224 WD="sesquilinear form" Disambiguation="on a complex vector space" Agda=is-sesquilinear-form-ℂ-Vector-Space}}
if it:

- is left additive: $f(x + y,z) = f(x,z) + f(y,z)$
- preserves scalar multiplication on the left: $f(ax, y) = af(x,y)$
- is right additive: $f(x,y+z) = f(x,y) + f(x,z)$
- conjugates scalar multiplication on the right: $f(x,ay) = \bar{a}f(x,y)$

(Conjugating multiplication on the right is consistent with Wikipedia and what
$n$Lab calls the "mathematician's convention," as opposed to what $n$Lab calls
the "physicist's convention.")

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Vector-Space l1 l2)
  (f : type-ℂ-Vector-Space V → type-ℂ-Vector-Space V → ℂ l1)
  where

  is-left-additive-prop-form-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-left-additive-prop-form-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ x →
        Π-Prop
          ( type-ℂ-Vector-Space V)
          ( λ y →
            Π-Prop
              ( type-ℂ-Vector-Space V)
              ( λ z →
                Id-Prop
                  ( ℂ-Set l1)
                  ( f (add-ℂ-Vector-Space V x y) z)
                  ( f x z +ℂ f y z))))

  is-left-additive-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-left-additive-form-ℂ-Vector-Space =
    type-Prop is-left-additive-prop-form-ℂ-Vector-Space

  preserves-scalar-mul-left-prop-form-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  preserves-scalar-mul-left-prop-form-ℂ-Vector-Space =
    Π-Prop
      ( ℂ l1)
      ( λ a →
        Π-Prop
          ( type-ℂ-Vector-Space V)
          ( λ x →
            Π-Prop
              ( type-ℂ-Vector-Space V)
              ( λ y →
                Id-Prop
                  ( ℂ-Set l1)
                  ( f (mul-ℂ-Vector-Space V a x) y)
                  ( a *ℂ f x y))))

  preserves-scalar-mul-left-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  preserves-scalar-mul-left-form-ℂ-Vector-Space =
    type-Prop preserves-scalar-mul-left-prop-form-ℂ-Vector-Space

  is-right-additive-prop-form-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-right-additive-prop-form-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ x →
        Π-Prop
          ( type-ℂ-Vector-Space V)
          ( λ y →
            Π-Prop
              ( type-ℂ-Vector-Space V)
              ( λ z →
                Id-Prop
                  ( ℂ-Set l1)
                  ( f x (add-ℂ-Vector-Space V y z))
                  ( f x y +ℂ f x z))))

  is-right-additive-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-right-additive-form-ℂ-Vector-Space =
    type-Prop is-right-additive-prop-form-ℂ-Vector-Space

  conjugates-scalar-mul-right-prop-form-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  conjugates-scalar-mul-right-prop-form-ℂ-Vector-Space =
    Π-Prop
      ( ℂ l1)
      ( λ a →
        Π-Prop
          ( type-ℂ-Vector-Space V)
          ( λ x →
            Π-Prop
              ( type-ℂ-Vector-Space V)
              ( λ y →
                Id-Prop
                  ( ℂ-Set l1)
                  ( f x (mul-ℂ-Vector-Space V a y))
                  ( conjugate-ℂ a *ℂ f x y))))

  conjugates-scalar-mul-right-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  conjugates-scalar-mul-right-form-ℂ-Vector-Space =
    type-Prop conjugates-scalar-mul-right-prop-form-ℂ-Vector-Space

  is-sesquilinear-prop-form-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-sesquilinear-prop-form-ℂ-Vector-Space =
    ( is-left-additive-prop-form-ℂ-Vector-Space) ∧
    ( preserves-scalar-mul-left-prop-form-ℂ-Vector-Space) ∧
    ( is-right-additive-prop-form-ℂ-Vector-Space) ∧
    ( conjugates-scalar-mul-right-prop-form-ℂ-Vector-Space)

  is-sesquilinear-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-sesquilinear-form-ℂ-Vector-Space =
    type-Prop is-sesquilinear-prop-form-ℂ-Vector-Space

sesquilinear-form-ℂ-Vector-Space :
  {l1 l2 : Level} → ℂ-Vector-Space l1 l2 → UU (lsuc l1 ⊔ l2)
sesquilinear-form-ℂ-Vector-Space V =
  type-subtype (is-sesquilinear-prop-form-ℂ-Vector-Space V)

module _
  {l1 l2 : Level}
  (V : ℂ-Vector-Space l1 l2)
  (f : sesquilinear-form-ℂ-Vector-Space V)
  where

  map-sesquilinear-form-ℂ-Vector-Space :
    type-ℂ-Vector-Space V → type-ℂ-Vector-Space V → ℂ l1
  map-sesquilinear-form-ℂ-Vector-Space = pr1 f
```

## External links

- [Sesquilinear form](https://en.wikipedia.org/wiki/Sesquilinear_form) on
  Wikipedia
