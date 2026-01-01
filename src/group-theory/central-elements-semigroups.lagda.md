# Central elements of semirings

```agda
module group-theory.central-elements-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

An element `x` of a semigroup `G` is said to be central if `xy ＝ yx` for every
`y : G`.

## Definition

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  is-central-element-prop-Semigroup : type-Semigroup G → Prop l
  is-central-element-prop-Semigroup x =
    Π-Prop
      ( type-Semigroup G)
      ( λ y →
        Id-Prop
          ( set-Semigroup G)
          ( mul-Semigroup G x y)
          ( mul-Semigroup G y x))

  is-central-element-Semigroup : type-Semigroup G → UU l
  is-central-element-Semigroup x =
    type-Prop (is-central-element-prop-Semigroup x)

  is-prop-is-central-element-Semigroup :
    (x : type-Semigroup G) → is-prop (is-central-element-Semigroup x)
  is-prop-is-central-element-Semigroup x =
    is-prop-type-Prop (is-central-element-prop-Semigroup x)
```

## Properties

### The product of two central elements is central

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  abstract
    is-central-element-mul-Semigroup :
      (x y : type-Semigroup G) →
      is-central-element-Semigroup G x → is-central-element-Semigroup G y →
      is-central-element-Semigroup G (mul-Semigroup G x y)
    is-central-element-mul-Semigroup x y H K z =
      ( associative-mul-Semigroup G x y z) ∙
      ( ap (mul-Semigroup G x) (K z)) ∙
      ( inv (associative-mul-Semigroup G x z y)) ∙
      ( ap (mul-Semigroup' G y) (H z)) ∙
      ( associative-mul-Semigroup G z x y)
```
