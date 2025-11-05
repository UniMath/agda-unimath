# Noncoherent H-spaces

```agda
module structured-types.noncoherent-h-spaces where
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

A {{#concept "noncoherent H-space" Agda=Noncoherent-H-Space}} is a
[pointed type](structured-types.pointed-types.md) `A`
[equipped](foundation.structure.md) with a binary operation `μ` and
[homotopies](foundation-core.homotopies.md) `(λ x → μ point x) ~ id` and
`(λ x → μ x point) ~ id`. If `A` is a [connected](foundation.connected-types.md)
H-space, then `λ x → μ a x` and `λ x → μ x a` are
[equivalences](foundation-core.equivalences.md) for each `a : A`.

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

### Noncoherent H-Spaces

```agda
noncoherent-h-space-structure :
  {l : Level} (A : Pointed-Type l) → UU l
noncoherent-h-space-structure A =
  Σ ( (x y : type-Pointed-Type A) → type-Pointed-Type A)
    ( λ μ → unit-laws μ (point-Pointed-Type A))

Noncoherent-H-Space : (l : Level) → UU (lsuc l)
Noncoherent-H-Space l = Σ (Pointed-Type l) (noncoherent-h-space-structure)

module _
  {l : Level} (A : Noncoherent-H-Space l)
  where

  pointed-type-Noncoherent-H-Space : Pointed-Type l
  pointed-type-Noncoherent-H-Space = pr1 A

  type-Noncoherent-H-Space : UU l
  type-Noncoherent-H-Space = type-Pointed-Type pointed-type-Noncoherent-H-Space

  point-Noncoherent-H-Space : type-Noncoherent-H-Space
  point-Noncoherent-H-Space =
    point-Pointed-Type pointed-type-Noncoherent-H-Space

  mul-Noncoherent-H-Space :
    type-Noncoherent-H-Space →
    type-Noncoherent-H-Space →
    type-Noncoherent-H-Space
  mul-Noncoherent-H-Space = pr1 (pr2 A)

  unit-laws-mul-Noncoherent-H-Space :
    unit-laws mul-Noncoherent-H-Space point-Noncoherent-H-Space
  unit-laws-mul-Noncoherent-H-Space = pr2 (pr2 A)

  left-unit-law-mul-Noncoherent-H-Space :
    (x : type-Noncoherent-H-Space) →
    mul-Noncoherent-H-Space point-Noncoherent-H-Space x ＝ x
  left-unit-law-mul-Noncoherent-H-Space = pr1 unit-laws-mul-Noncoherent-H-Space

  right-unit-law-mul-Noncoherent-H-Space :
    (x : type-Noncoherent-H-Space) →
    mul-Noncoherent-H-Space x point-Noncoherent-H-Space ＝ x
  right-unit-law-mul-Noncoherent-H-Space = pr2 unit-laws-mul-Noncoherent-H-Space
```
