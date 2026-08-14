# Bands

```agda
module group-theory.bands where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.idempotent-elements-semigroups
open import group-theory.semigroups

open import structured-types.magmas
```

</details>

## Idea

A {{#concept "band" Agda=Band}} is a [semigroup](group-theory.semigroups.md) in which every element is [idempotent](group-theory.idempotent-elements-semigroups.md).

## Definition

### The predicate of being a band

```agda
module _
  {l1 : Level} (G : Semigroup l1)
  where

  is-band-Semigroup : UU l1
  is-band-Semigroup =
    (x : type-Semigroup G) → is-idempotent-element-Semigroup G x

  is-prop-is-band-Semigroup :
    is-prop is-band-Semigroup
  is-prop-is-band-Semigroup =
    is-prop-Π (is-prop-is-idempotent-element-Semigroup G)

  is-band-prop-Semigroup :
    Prop l1
  pr1 is-band-prop-Semigroup = is-band-Semigroup
  pr2 is-band-prop-Semigroup = is-prop-is-band-Semigroup
```

### The type of bands

```agda
Band : (l : Level) → UU (lsuc l)
Band l = Σ (Semigroup l) is-band-Semigroup

module _
  {l1 : Level} (B : Band l1)
  where

  semigroup-Band : Semigroup l1
  semigroup-Band = pr1 B

  is-band-Band : is-band-Semigroup semigroup-Band
  is-band-Band = pr2 B

  set-Band : Set l1
  set-Band = set-Semigroup semigroup-Band

  type-Band : UU l1
  type-Band = type-Semigroup semigroup-Band

  is-set-type-Band : is-set type-Band
  is-set-type-Band = is-set-type-Semigroup semigroup-Band

  mul-Band : type-Band → type-Band → type-Band
  mul-Band = mul-Semigroup semigroup-Band

  mul-Band' : type-Band → type-Band → type-Band
  mul-Band' = mul-Semigroup' semigroup-Band

  ap-mul-Band :
    {x x' y y' : type-Band} →
    x ＝ x' → y ＝ y' → mul-Band x y ＝ mul-Band x' y'
  ap-mul-Band = ap-mul-Semigroup semigroup-Band

  associative-mul-Band :
    (x y z : type-Band) → mul-Band (mul-Band x y) z ＝ mul-Band x (mul-Band y z)
  associative-mul-Band = associative-mul-Semigroup semigroup-Band

  left-swap-mul-Band :
    {x y z : type-Band} → mul-Band x y ＝ mul-Band y x →
    mul-Band x (mul-Band y z) ＝
    mul-Band y (mul-Band x z)
  left-swap-mul-Band =
    left-swap-mul-Semigroup semigroup-Band

  right-swap-mul-Band :
    {x y z : type-Band} → mul-Band y z ＝ mul-Band z y →
    mul-Band (mul-Band x y) z ＝
    mul-Band (mul-Band x z) y
  right-swap-mul-Band =
    right-swap-mul-Semigroup semigroup-Band

  interchange-mul-mul-Band :
    {x y z w : type-Band} → mul-Band y z ＝ mul-Band z y →
    mul-Band (mul-Band x y) (mul-Band z w) ＝
    mul-Band (mul-Band x z) (mul-Band y w)
  interchange-mul-mul-Band =
    interchange-mul-mul-Semigroup semigroup-Band

  magma-Band : Magma l1
  magma-Band = magma-Semigroup semigroup-Band
```

