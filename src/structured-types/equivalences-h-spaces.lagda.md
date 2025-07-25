# Equivalences of H-spaces

```agda
module structured-types.equivalences-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import group-theory.homomorphisms-semigroups

open import structured-types.h-spaces
open import structured-types.morphisms-h-spaces
open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Consider two [H-spaces](structured-types.h-spaces.md) `X` and `Y`. An
{{#concept "equivalence of H-spaces" Agda=equiv-H-Space}} from `X` to `Y`
consists of a [pointed equivalence](structured-types.pointed-equivalences.md)
`e : X ≃∗ Y` that preserves the unital binary operation

```text
  α : (x x' : X) → e (μ x x') ＝ μ (e x) (e x')
```

and which furthermore comes equipped with the following structure, witnessing
that the unit laws are preserved:

- For each `x' : X` an identification `α₁ x'` witnessing that the triangle

  ```text
                              α * x'
                  e (μ * x') -------> μ (e *) (e x')
                        \                 /
                         \               / ap (μ - (e x')) e₁
                          \             /
                           \           ∨
    ap e (left-unit-law x') \       μ * (e x')
                             \       /
                              \     / left-unit-law (e x')
                               \   /
                                ∨ ∨
                                e x'
  ```

  commutes.

- For each `x : X` an identification `α₂ x` witnessing that the triangle

  ```text
                              α x *
                  e (μ x *) --------> μ (e x) (e *)
                        \                 /
                         \               / ap (μ (e x) -) e₁
                          \             /
                           \           ∨
    ap e (right-unit-law x) \       μ (e x) *
                             \       /
                              \     / right-unit-law (e x)
                               \   /
                                ∨ ∨
                                e x
  ```

  commutes.

- An identification `α₃` witnessing that the square

  ```text
                                                     α₁
     α₀ * * ∙ (ap (μ - (e *)) e₁ ∙ left-unit-law *) ---> ap e (left-unit-law *)
                       |                                         |
         (α₀ * *) ·l β |                                         |
                       ∨                                         ∨
    α₀ * * ∙ (ap (μ (e *) -) e₁ ∙ right-unit-law *) ---> ap e (right-unit-law *)
                                                     α₂
  ```

  Here, the identification on the left is obtained by left whiskering the
  identification witnessing that the square

  ```text
                               ap (μ (e *)) e₁
                μ (e *) (e *) -----------------> μ (e *) *
                      |                               |
    ap (μ - (e *)) e₁ |                 β             | right-unit-law (e *)
                      ∨                               ∨
                   μ * (e *) ----------------------> e *
                               left-unit-law (e *)
  ```

  commutes, with the identification `α * * : e (μ * *) ＝ μ (e *) (e *)`. The
  quickest way to see that this square commutes is by identification elimination
  on the identification `e₁ : e * ＝ *`, using the coherence
  `left-unit-law * ＝ right-unit-law *`. Alternatively, note that all the
  squares in the diagram

  ```text
                               ap (μ (e *)) e₁
                μ (e *) (e *) -----------------> μ (e *) * --------> e *
                      |                               |               |
    ap (μ - (e *)) e₁ |                 ap (μ - *) e₁ |               |
                      ∨                               ∨               ∨
                   μ * (e *) ---------------------> μ * * ----------> *
                      |            ap (μ *) e₁        |               |
                      |                               |  coh ·r refl  | refl
                      ∨                               ∨               ∨
                     e * ---------------------------> * ------------> *
                                       e₁                  refl
  ```

  commute. Therefore we obtain an identification

  ```text
    ap (μ - (e *)) e₁ ∙ (left-unit-law (e *) ∙ e₁) ＝
    ap (μ (e *) -) e₁ ∙ (right-unit-law (e *) ∙ e₁).
  ```

  By unwhiskering of commuting squares of identifications, i.e., by canceling
  out `e₁` on both sides, it follows that the asserted square commutes.

## Definition

### The predicate of preserving H-space structure on a pointed type

```agda
module _
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2)
  where

  preserves-mul-pointed-equiv-H-Space :
    (pointed-type-H-Space M ≃∗ pointed-type-H-Space N) → UU (l1 ⊔ l2)
  preserves-mul-pointed-equiv-H-Space e =
    preserves-mul-pointed-map-H-Space M N (pointed-map-pointed-equiv e)

  preserves-left-unit-law-mul-pointed-equiv-H-Space :
    (e : pointed-type-H-Space M ≃∗ pointed-type-H-Space N) →
    preserves-mul-pointed-equiv-H-Space e → UU (l1 ⊔ l2)
  preserves-left-unit-law-mul-pointed-equiv-H-Space e =
    preserves-left-unit-law-mul-pointed-map-H-Space M N
      ( pointed-map-pointed-equiv e)

  preserves-right-unit-law-mul-pointed-equiv-H-Space :
    (e : pointed-type-H-Space M ≃∗ pointed-type-H-Space N) →
    preserves-mul-pointed-equiv-H-Space e → UU (l1 ⊔ l2)
  preserves-right-unit-law-mul-pointed-equiv-H-Space e =
    preserves-right-unit-law-mul-pointed-map-H-Space M N
      ( pointed-map-pointed-equiv e)

  preserves-coherence-unit-laws-mul-pointed-equiv-H-Space :
    (e : pointed-type-H-Space M ≃∗ pointed-type-H-Space N) →
    (μ : preserves-mul-pointed-equiv-H-Space e) →
    (ν : preserves-left-unit-law-mul-pointed-equiv-H-Space e μ) →
    (ρ : preserves-right-unit-law-mul-pointed-equiv-H-Space e μ) → UU l2
  preserves-coherence-unit-laws-mul-pointed-equiv-H-Space e =
    preserves-coherence-unit-laws-mul-pointed-map-H-Space M N
      ( pointed-map-pointed-equiv e)

  preserves-unital-mul-pointed-equiv-H-Space :
    (e : pointed-type-H-Space M ≃∗ pointed-type-H-Space N) →
    UU (l1 ⊔ l2)
  preserves-unital-mul-pointed-equiv-H-Space e =
    preserves-unital-mul-pointed-map-H-Space M N (pointed-map-pointed-equiv e)
```

### Equivalences of H-spaces

```agda
module _
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2)
  where

  equiv-H-Space : UU (l1 ⊔ l2)
  equiv-H-Space =
    Σ ( pointed-type-H-Space M ≃∗ pointed-type-H-Space N)
      ( preserves-unital-mul-pointed-equiv-H-Space M N)

module _
  {l1 l2 : Level} {M : H-Space l1} {N : H-Space l2} (e : equiv-H-Space M N)
  where

  pointed-equiv-equiv-H-Space : pointed-type-H-Space M ≃∗ pointed-type-H-Space N
  pointed-equiv-equiv-H-Space = pr1 e

  map-equiv-H-Space : type-H-Space M → type-H-Space N
  map-equiv-H-Space = map-pointed-equiv pointed-equiv-equiv-H-Space

  preserves-unit-equiv-H-Space :
    map-equiv-H-Space (unit-H-Space M) ＝ unit-H-Space N
  preserves-unit-equiv-H-Space =
    preserves-point-pointed-equiv pointed-equiv-equiv-H-Space

  preserves-unital-mul-equiv-H-Space :
    preserves-unital-mul-pointed-equiv-H-Space M N pointed-equiv-equiv-H-Space
  preserves-unital-mul-equiv-H-Space = pr2 e

  preserves-mul-equiv-H-Space :
    preserves-mul-pointed-equiv-H-Space M N pointed-equiv-equiv-H-Space
  preserves-mul-equiv-H-Space =
    pr1 preserves-unital-mul-equiv-H-Space

  preserves-left-unit-law-mul-equiv-H-Space :
    preserves-left-unit-law-mul-pointed-equiv-H-Space M N
      ( pointed-equiv-equiv-H-Space)
      ( preserves-mul-equiv-H-Space)
  preserves-left-unit-law-mul-equiv-H-Space =
    pr1 (pr2 preserves-unital-mul-equiv-H-Space)

  preserves-right-unit-law-mul-equiv-H-Space :
    preserves-right-unit-law-mul-pointed-equiv-H-Space M N
      ( pointed-equiv-equiv-H-Space)
      ( preserves-mul-equiv-H-Space)
  preserves-right-unit-law-mul-equiv-H-Space =
    pr1 (pr2 (pr2 preserves-unital-mul-equiv-H-Space))

  preserves-coherence-unit-laws-mul-equiv-H-Space :
    preserves-coherence-unit-laws-mul-pointed-equiv-H-Space M N
      ( pointed-equiv-equiv-H-Space)
      ( preserves-mul-equiv-H-Space)
      ( preserves-left-unit-law-mul-equiv-H-Space)
      ( preserves-right-unit-law-mul-equiv-H-Space)
  preserves-coherence-unit-laws-mul-equiv-H-Space =
    pr2 (pr2 (pr2 preserves-unital-mul-equiv-H-Space))
```
