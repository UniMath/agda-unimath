# Nilpotent elements in semirings

```agda
module ring-theory.nilpotent-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.binomial-theorem-semirings
open import ring-theory.powers-of-elements-semirings
open import ring-theory.semirings
```

</details>

## Idea

A
{{#concept "nilpotent element" Disambiguation="in a semiring" Agda=is-nilpotent-element-Semiring}}
in a [semiring](ring-theory.semirings.md) is an element `x` for which there is a
[natural number](elementary-number-theory.natural-numbers.md) `n` such that
`xⁿ = 0`.

## Definition

```agda
is-nilpotent-element-semiring-Prop :
  {l : Level} (R : Semiring l) → type-Semiring R → Prop l
is-nilpotent-element-semiring-Prop R x =
  exists-structure-Prop ℕ (λ n → power-Semiring R n x ＝ zero-Semiring R)

is-nilpotent-element-Semiring :
  {l : Level} (R : Semiring l) → type-Semiring R → UU l
is-nilpotent-element-Semiring R x =
  type-Prop (is-nilpotent-element-semiring-Prop R x)

is-prop-is-nilpotent-element-Semiring :
  {l : Level} (R : Semiring l) (x : type-Semiring R) →
  is-prop (is-nilpotent-element-Semiring R x)
is-prop-is-nilpotent-element-Semiring R x =
  is-prop-type-Prop (is-nilpotent-element-semiring-Prop R x)
```

## Properties

### Zero is nilpotent

```agda
is-nilpotent-zero-Semiring :
  {l : Level} (R : Semiring l) →
  is-nilpotent-element-Semiring R (zero-Semiring R)
is-nilpotent-zero-Semiring R = intro-exists 1 refl
```

### If `x` and `y` commute and are both nilpotent, then `x + y` is nilpotent

```agda
is-nilpotent-add-Semiring :
  {l : Level} (R : Semiring l) →
  (x y : type-Semiring R) → (mul-Semiring R x y ＝ mul-Semiring R y x) →
  is-nilpotent-element-Semiring R x → is-nilpotent-element-Semiring R y →
  is-nilpotent-element-Semiring R (add-Semiring R x y)
is-nilpotent-add-Semiring R x y H f h =
  apply-universal-property-trunc-Prop f
    ( is-nilpotent-element-semiring-Prop R (add-Semiring R x y))
    ( λ (n , p) →
      apply-universal-property-trunc-Prop h
        ( is-nilpotent-element-semiring-Prop R (add-Semiring R x y))
        ( λ (m , q) →
          intro-exists
            ( n +ℕ m)
            ( ( is-linear-combination-power-add-Semiring R n m x y H) ∙
              ( ( ap-add-Semiring R
                  ( ( ap (mul-Semiring' R _) q) ∙
                    ( left-zero-law-mul-Semiring R _))
                  ( ( ap (mul-Semiring' R _) p) ∙
                    ( left-zero-law-mul-Semiring R _))) ∙
                ( left-unit-law-add-Semiring R (zero-Semiring R))))))
```

### If `x` is nilpotent and `y` commutes with `x`, then `xy` is also nilpotent

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-nilpotent-element-mul-Semiring :
    (x y : type-Semiring R) →
    mul-Semiring R x y ＝ mul-Semiring R y x →
    is-nilpotent-element-Semiring R x →
    is-nilpotent-element-Semiring R (mul-Semiring R x y)
  is-nilpotent-element-mul-Semiring x y H f =
    apply-universal-property-trunc-Prop f
      ( is-nilpotent-element-semiring-Prop R (mul-Semiring R x y))
      ( λ (n , p) →
        intro-exists n
          ( ( distributive-power-mul-Semiring R n H) ∙
            ( ( ap (mul-Semiring' R (power-Semiring R n y)) p) ∙
              ( left-zero-law-mul-Semiring R
                ( power-Semiring R n y)))))

  is-nilpotent-element-mul-Semiring' :
    (x y : type-Semiring R) →
    mul-Semiring R x y ＝ mul-Semiring R y x →
    is-nilpotent-element-Semiring R x →
    is-nilpotent-element-Semiring R (mul-Semiring R y x)
  is-nilpotent-element-mul-Semiring' x y H f =
    is-closed-under-eq-subtype
      ( is-nilpotent-element-semiring-Prop R)
      ( is-nilpotent-element-mul-Semiring x y H f)
      ( H)
```
