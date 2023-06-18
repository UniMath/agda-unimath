# H-spaces

```agda
module structured-types.h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

An H-space is a pointed type `A` equipped with a binary operation `μ` and
homotopies `(λ x → μ point x) ~ id` and `λ x → μ x point ~ id`. If `A` is a
connected H-space, then `λ x → μ a x` and `λ x → μ x a` are equivalences for
each `a : A`.

## Definitions

### Unital binary operations on pointed types

```agda
unit-laws-mul-Pointed-Type :
  {l : Level} (A : Pointed-Type l)
  (μ : (x y : type-Pointed-Type A) → type-Pointed-Type A) → UU l
unit-laws-mul-Pointed-Type A μ = unit-laws μ (point-Pointed-Type A)

unital-mul-Pointed-Type :
  {l : Level} → Pointed-Type l → UU l
unital-mul-Pointed-Type A =
  Σ ( type-Pointed-Type A → type-Pointed-Type A → type-Pointed-Type A)
    ( unit-laws-mul-Pointed-Type A)
```

### H-Spaces

```agda
h-space-structure :
  {l : Level} (A : Pointed-Type l) → UU l
h-space-structure A =
  Σ ( (x y : type-Pointed-Type A) → type-Pointed-Type A)
    ( λ μ → unit-laws μ (point-Pointed-Type A))

H-Space : (l : Level) → UU (lsuc l)
H-Space l = Σ (Pointed-Type l) h-space-structure

module _
  {l : Level} (A : H-Space l)
  where

  pointed-type-H-Space : Pointed-Type l
  pointed-type-H-Space = pr1 A

  type-H-Space : UU l
  type-H-Space = type-Pointed-Type pointed-type-H-Space

  point-H-Space : type-H-Space
  point-H-Space = point-Pointed-Type pointed-type-H-Space

  mul-H-Space : type-H-Space → type-H-Space → type-H-Space
  mul-H-Space = pr1 (pr2 A)

  unit-laws-mul-H-Space :
    unit-laws mul-H-Space point-H-Space
  unit-laws-mul-H-Space = pr2 (pr2 A)

  left-unit-law-mul-H-Space :
    (x : type-H-Space) → Id (mul-H-Space point-H-Space x) x
  left-unit-law-mul-H-Space = pr1 unit-laws-mul-H-Space

  right-unit-law-mul-H-Space :
    (x : type-H-Space) → Id (mul-H-Space x point-H-Space) x
  right-unit-law-mul-H-Space = pr2 unit-laws-mul-H-Space
```
