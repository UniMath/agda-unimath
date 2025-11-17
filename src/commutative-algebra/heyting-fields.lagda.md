# Heyting fields

```agda
module commutative-algebra.heyting-fields where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.invertible-elements-commutative-rings
open import commutative-algebra.local-commutative-rings
open import commutative-algebra.trivial-commutative-rings

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "Heyting field" WDID=Q5749811 WD="Heyting field" Agda=Heyting-Field}}
is a [local commutative ring](commutative-algebra.local-commutative-rings.md)
with the properties:

- it is [nontrivial](commutative-algebra.trivial-commutative-rings.md): 0 ≠ 1
- any
  [non](foundation.negation.md)[invertible](commutative-algebra.invertible-elements-commutative-rings.md)
  elements are [equal](foundation.identity-types.md) to zero

## Definition

```agda
is-heyting-field-prop-Local-Commutative-Ring :
  {l : Level} → Local-Commutative-Ring l → Prop l
is-heyting-field-prop-Local-Commutative-Ring R =
  ( is-nontrivial-commutative-ring-Prop
    ( commutative-ring-Local-Commutative-Ring R)) ∧
  ( Π-Prop
    ( type-Local-Commutative-Ring R)
    ( λ x →
      hom-Prop
        ( ¬'
          ( is-invertible-element-prop-Commutative-Ring
            ( commutative-ring-Local-Commutative-Ring R)
            ( x)))
        ( is-zero-prop-Local-Commutative-Ring R x)))

is-heyting-field-Local-Commutative-Ring :
  {l : Level} → Local-Commutative-Ring l → UU l
is-heyting-field-Local-Commutative-Ring R =
  type-Prop (is-heyting-field-prop-Local-Commutative-Ring R)

Heyting-Field : (l : Level) → UU (lsuc l)
Heyting-Field l =
  type-subtype (is-heyting-field-prop-Local-Commutative-Ring {l})
```

## Properties

```agda
module _
  {l : Level}
  (F : Heyting-Field l)
  where

  local-commutative-ring-Heyting-Field : Local-Commutative-Ring l
  local-commutative-ring-Heyting-Field = pr1 F

  commutative-ring-Heyting-Field : Commutative-Ring l
  commutative-ring-Heyting-Field =
    commutative-ring-Local-Commutative-Ring local-commutative-ring-Heyting-Field

  ring-Heyting-Field : Ring l
  ring-Heyting-Field = ring-Commutative-Ring commutative-ring-Heyting-Field

  type-Heyting-Field : UU l
  type-Heyting-Field = type-Ring ring-Heyting-Field

  set-Heyting-Field : Set l
  set-Heyting-Field = set-Ring ring-Heyting-Field

  zero-Heyting-Field : type-Heyting-Field
  zero-Heyting-Field = zero-Ring ring-Heyting-Field

  one-Heyting-Field : type-Heyting-Field
  one-Heyting-Field = one-Ring ring-Heyting-Field

  add-Heyting-Field :
    type-Heyting-Field → type-Heyting-Field → type-Heyting-Field
  add-Heyting-Field = add-Ring ring-Heyting-Field

  mul-Heyting-Field :
    type-Heyting-Field → type-Heyting-Field → type-Heyting-Field
  mul-Heyting-Field = mul-Ring ring-Heyting-Field

  neg-Heyting-Field : type-Heyting-Field → type-Heyting-Field
  neg-Heyting-Field = neg-Ring ring-Heyting-Field
```
