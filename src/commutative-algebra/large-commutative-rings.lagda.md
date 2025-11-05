# Large commutative rings

```agda
module commutative-algebra.large-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.sets
open import foundation.universe-levels

open import group-theory.large-commutative-monoids

open import ring-theory.large-rings
```

</details>

## Idea

A {{#concept "large commutative ring" Agda=Large-Ring}} is a
[large ring](ring-theory.large-rings.md) with a commutative multiplicative
operation.

## Definition

```agda
record Large-Commutative-Ring
  (α : Level → Level) (β : Level → Level → Level) : UUω where

  constructor
    make-Large-Commutative-Ring

  field
    large-ring-Large-Commutative-Ring : Large-Ring α β

  type-Large-Commutative-Ring : (l : Level) → UU (α l)
  type-Large-Commutative-Ring =
    type-Large-Ring large-ring-Large-Commutative-Ring

  set-Large-Commutative-Ring : (l : Level) → Set (α l)
  set-Large-Commutative-Ring = set-Large-Ring large-ring-Large-Commutative-Ring

  add-Large-Commutative-Ring :
    {l1 l2 : Level} →
    type-Large-Commutative-Ring l1 →
    type-Large-Commutative-Ring l2 →
    type-Large-Commutative-Ring (l1 ⊔ l2)
  add-Large-Commutative-Ring = add-Large-Ring large-ring-Large-Commutative-Ring

  zero-Large-Commutative-Ring : type-Large-Commutative-Ring lzero
  zero-Large-Commutative-Ring =
    zero-Large-Ring large-ring-Large-Commutative-Ring

  sim-prop-Large-Commutative-Ring :
    Large-Relation-Prop β type-Large-Commutative-Ring
  sim-prop-Large-Commutative-Ring =
    sim-prop-Large-Ring large-ring-Large-Commutative-Ring

  sim-Large-Commutative-Ring : Large-Relation β type-Large-Commutative-Ring
  sim-Large-Commutative-Ring = sim-Large-Ring large-ring-Large-Commutative-Ring

  raise-Large-Commutative-Ring :
    {l1 : Level} (l2 : Level) (x : type-Large-Commutative-Ring l1) →
    type-Large-Commutative-Ring (l1 ⊔ l2)
  raise-Large-Commutative-Ring =
    raise-Large-Ring large-ring-Large-Commutative-Ring

  mul-Large-Commutative-Ring :
    {l1 l2 : Level} →
    type-Large-Commutative-Ring l1 →
    type-Large-Commutative-Ring l2 →
    type-Large-Commutative-Ring (l1 ⊔ l2)
  mul-Large-Commutative-Ring = mul-Large-Ring large-ring-Large-Commutative-Ring

  field
    commutative-mul-Large-Commutative-Ring :
      {l1 l2 : Level} →
      (a : type-Large-Commutative-Ring l1) →
      (b : type-Large-Commutative-Ring l2) →
      mul-Large-Commutative-Ring a b ＝ mul-Large-Commutative-Ring b a

open Large-Commutative-Ring public
```

## Properties

### Small commutative rings from large commutative rings

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  commutative-ring-Large-Commutative-Ring : (l : Level) → Commutative-Ring (α l)
  commutative-ring-Large-Commutative-Ring l =
    ( ring-Large-Ring (large-ring-Large-Commutative-Ring R) l ,
      commutative-mul-Large-Commutative-Ring R)
```

### The multiplicative large commutative monoid of a large commutative ring

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  multiplicative-large-commutative-monoid-Large-Commutative-Ring :
    Large-Commutative-Monoid α β
  multiplicative-large-commutative-monoid-Large-Commutative-Ring =
    make-Large-Commutative-Monoid
      ( multiplicative-large-monoid-Large-Ring
        ( large-ring-Large-Commutative-Ring R))
      ( commutative-mul-Large-Commutative-Ring R)
```
