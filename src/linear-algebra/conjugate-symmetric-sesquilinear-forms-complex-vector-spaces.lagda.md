# Conjugate symmetric sesquilinear forms in complex vector spaces

```agda
module linear-algebra.conjugate-symmetric-sesquilinear-forms-complex-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.real-complex-numbers

open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.complex-vector-spaces
open import linear-algebra.sesquilinear-forms-complex-vector-spaces
```

</details>

## Idea

A
[sesquilinear form](linear-algebra.sesquilinear-forms-complex-vector-spaces.md)
`f` in a [complex vector space](linear-algebra.complex-vector-spaces.md) is
{{#concept "conjugate symmetric" Disambiguation="sesquilinear form in a complex vector space" Agda=is-conjugate-symmetric-sesquilinear-form-ℂ-Vector-Space}}
if `f x y` is the
[complex conjugate](complex-numbers.conjugation-complex-numbers.md) of `f y x`
for all `x` and `y`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Vector-Space l1 l2)
  (f : sesquilinear-form-ℂ-Vector-Space V)
  where

  is-conjugate-symmetric-prop-sesquilinear-form-ℂ-Vector-Space :
    Prop (lsuc l1 ⊔ l2)
  is-conjugate-symmetric-prop-sesquilinear-form-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ x →
        Π-Prop
          ( type-ℂ-Vector-Space V)
          ( λ y →
            Id-Prop
              ( ℂ-Set l1)
              ( map-sesquilinear-form-ℂ-Vector-Space V f x y)
              ( conjugate-ℂ (map-sesquilinear-form-ℂ-Vector-Space V f y x))))

  is-conjugate-symmetric-sesquilinear-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-conjugate-symmetric-sesquilinear-form-ℂ-Vector-Space =
    type-Prop is-conjugate-symmetric-prop-sesquilinear-form-ℂ-Vector-Space
```

## Properties

### The diagonal of a conjugate symmetric sesquilinear form is real

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Vector-Space l1 l2)
  (f : sesquilinear-form-ℂ-Vector-Space V)
  where

  abstract
    is-real-diagonal-is-conjugate-symmetric-sesquilinear-form-ℂ-Vector-Space :
      is-conjugate-symmetric-sesquilinear-form-ℂ-Vector-Space V f →
      (v : type-ℂ-Vector-Space V) →
      is-real-ℂ (map-sesquilinear-form-ℂ-Vector-Space V f v v)
    is-real-diagonal-is-conjugate-symmetric-sesquilinear-form-ℂ-Vector-Space
      H v = is-real-eq-conjugate-ℂ _ ( inv (H v v))
```

## External links

- [Conjugate symmetry](https://en.wikipedia.org/wiki/Even_and_odd_functions#Complex-valued_functions)
  on Wikipedia
