# Nuclei on large locales

```agda
module order-theory.nuclei-large-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.homomorphisms-large-meet-semilattices
open import order-theory.large-locales
```

</details>

## Idea

A **nucleus** on a [large locale](order-theory.large-locales.md) `L` is an order
preserving map `j : hom-Large-Poset id L L` such that `j` preserves meets and is idempotent.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Locale α β)
  where

  record
    nucleus-Large-Locale : UUω
    where
    field
      hom-large-meet-semilattice-nucleus-Large-Locale :
        hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Locale L)
          ( large-meet-semilattice-Large-Locale L)
      is-increasing-nucleus-Large-Locale :
        {l1 : Level} (x : type-Large-Locale L l1) →
        leq-Large-Locale L x
          ( map-hom-Large-Meet-Semilattice
            ( large-meet-semilattice-Large-Locale L)
            ( large-meet-semilattice-Large-Locale L)
            ( hom-large-meet-semilattice-nucleus-Large-Locale)
            ( x))
      is-idempotent-nucleus-Large-Locale :
        {l1 : Level} (x : type-Large-Locale L l1) →
        map-hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Locale L)
          ( large-meet-semilattice-Large-Locale L)
          ( hom-large-meet-semilattice-nucleus-Large-Locale)
          ( map-hom-Large-Meet-Semilattice
            ( large-meet-semilattice-Large-Locale L)
            ( large-meet-semilattice-Large-Locale L)
            ( hom-large-meet-semilattice-nucleus-Large-Locale)
            ( x)) ＝
        map-hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Locale L)
          ( large-meet-semilattice-Large-Locale L)
          ( hom-large-meet-semilattice-nucleus-Large-Locale)
          ( x)

  open nucleus-Large-Locale public

  module _
    (j : nucleus-Large-Locale)
    where

    map-nucleus-Large-Locale :
      {l1 : Level} → type-Large-Locale L l1 → type-Large-Locale L l1
    map-nucleus-Large-Locale =
      map-hom-Large-Meet-Semilattice
        ( large-meet-semilattice-Large-Locale L)
        ( large-meet-semilattice-Large-Locale L)
        ( hom-large-meet-semilattice-nucleus-Large-Locale j)

    preserves-order-nucleus-Large-Locale :
      {l1 l2 : Level}
      (x : type-Large-Locale L l1)
      (y : type-Large-Locale L l2) →
      leq-Large-Locale L x y →
      leq-Large-Locale L
        ( map-nucleus-Large-Locale x)
        ( map-nucleus-Large-Locale y)
    preserves-order-nucleus-Large-Locale =
      preserves-order-hom-Large-Meet-Semilattice
        ( large-meet-semilattice-Large-Locale L)
        ( large-meet-semilattice-Large-Locale L)
        ( hom-large-meet-semilattice-nucleus-Large-Locale j)

    preserves-meets-nucleus-Large-Locale :
      {l1 l2 : Level}
      (x : type-Large-Locale L l1)
      (y : type-Large-Locale L l2) →
      map-nucleus-Large-Locale (meet-Large-Locale L x y) ＝
      meet-Large-Locale L
        ( map-nucleus-Large-Locale x)
        ( map-nucleus-Large-Locale y)
    preserves-meets-nucleus-Large-Locale =
      preserves-meets-hom-Large-Meet-Semilattice
        ( hom-large-meet-semilattice-nucleus-Large-Locale j)

    preserves-top-nucleus-Large-Locale :
      map-nucleus-Large-Locale (top-Large-Locale L) ＝ top-Large-Locale L
    preserves-top-nucleus-Large-Locale =
      preserves-top-hom-Large-Meet-Semilattice
        ( hom-large-meet-semilattice-nucleus-Large-Locale j)
```

### The `j`-closed elements of a nuceus

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Locale α β) (j : nucleus-Large-Locale L)
  where

  is-closed-element-nucleus-Large-Locale-Prop :
    {l1 : Level} → type-Large-Locale L l1 → Prop (α l1)
  is-closed-element-nucleus-Large-Locale-Prop {l1} x =
    Id-Prop (set-Large-Locale L l1) (map-nucleus-Large-Locale L j x) x

  is-closed-element-nucleus-Large-Locale :
    {l1 : Level} → type-Large-Locale L l1 → UU (α l1)
  is-closed-element-nucleus-Large-Locale x =
    type-Prop (is-closed-element-nucleus-Large-Locale-Prop x)

  is-prop-is-closed-element-nucleus-Large-Locale :
    {l1 : Level} (x : type-Large-Locale L l1) →
    is-prop (is-closed-element-nucleus-Large-Locale x)
  is-prop-is-closed-element-nucleus-Large-Locale x =
    is-prop-type-Prop (is-closed-element-nucleus-Large-Locale-Prop x)

  closed-element-nucleus-Large-Locale :
    (l1 : Level) → UU (α l1)
  closed-element-nucleus-Large-Locale l1 =
    type-subtype (is-closed-element-nucleus-Large-Locale-Prop {l1})
```

## Properties

### The `j`-closed elements of a nucleus on a Locale form a subframe, and hence a quotient locale of `L`.

```agda

```
