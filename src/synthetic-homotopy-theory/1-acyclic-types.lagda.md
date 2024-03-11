# `1`-acyclic types

```agda
module synthetic-homotopy-theory.1-acyclic-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.binary-transport
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.0-acyclic-types
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.truncated-acyclic-maps
open import synthetic-homotopy-theory.truncated-acyclic-types
```

</details>

## Idea

A type is **`1`-acyclic** if its
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`1`-connected](foundation.connected-types.md).

We can characterize the `1`-acyclic types as the
[`0`-connected types](foundation.0-connected-types.md).

In one direction, our proof relies on the following group-theoretic fact: the
map of [generators](group-theory.generating-elements-groups.md) from a
[set](foundation-core.sets.md) `X` to the free group on `X` is
[injective](foundation-core.injective-maps.md). This is proved constructively in
{{#cite MRR88}} by Mines, Richman and Ruitenburg, and carried out in HoTT/UF and
formalized in Agda in {{#cite BCDE21}} by Bezem, Coquand, Dybjer, and Escardó.

Translated to [concrete groups](group-theory.concrete-groups.md) this means that
for every set `X`, we have a [pointed](structured-types.pointed-types.md)
[`1`-type](foundation-core.1-types.md) `pt : BG` together with an injection
`gen : X → pt ＝ pt`. (Actually, `BG` is `0`-connected as well, but we don't use
this in our proof below.)

A construction on the level of concrete groups can be found in the recent
preprint by David Wärn {{#cite Warn23draft}}.

For the time being, we haven't formalized this group-theoretic fact; instead we
label it as an explicit assumption of our proof.

## Definition

```agda
module _
  {l : Level} (A : UU l)
  where

  is-1-acyclic-Prop : Prop l
  is-1-acyclic-Prop = is-truncated-acyclic-Prop (one-𝕋) A

  is-1-acyclic : UU l
  is-1-acyclic = type-Prop is-1-acyclic-Prop

  is-prop-is-1-acyclic : is-prop is-1-acyclic
  is-prop-is-1-acyclic = is-prop-type-Prop is-1-acyclic-Prop
```

## Properties

### Every `0`-connected type is `1`-acyclic

```agda
module _
  {l : Level} (A : UU l)
  where

  is-1-acyclic-is-0-connected : is-0-connected A → is-1-acyclic A
  is-1-acyclic-is-0-connected = is-truncated-acyclic-succ-is-connected
```

### Every `1`-acyclic type is `0`-connected

As explained at the top "Idea" section, we turn the necessary group-theoretic
fact into an explicit assumption of our proof.

```agda
private
  record
    concrete-group-assumption' {l : Level} (A : UU l) : UU (lsuc l)
    where
    field
      BG : Truncated-Type l (one-𝕋)
      pt : type-Truncated-Type BG
      gen : A → type-Ω (pair (type-Truncated-Type BG) pt)
      is-injective-gen : is-injective gen

  concrete-group-assumption : UUω
  concrete-group-assumption =
    {l : Level} (A : UU l) → concrete-group-assumption' A

module _
  (cga : concrete-group-assumption)
  where

  is-contr-is-1-acyclic-is-set :
    {l : Level} (A : UU l) →
    is-set A → is-1-acyclic A → is-contr A
  is-contr-is-1-acyclic-is-set A s ac =
    let open concrete-group-assumption' (cga A) in
    is-contr-is-inhabited-is-prop
      ( is-prop-all-elements-equal
        ( λ x y →
          is-injective-gen
            ( binary-tr
              ( Id)
              ( htpy-eq
                ( is-section-map-inv-equiv
                  ( const A (type-Ω (pair (type-Truncated-Type BG) pt)) ,
                    is-equiv-const-Id-is-acyclic-Truncated-Type A ac BG pt pt)
                  ( gen))
                ( x))
              ( htpy-eq
                ( is-section-map-inv-equiv
                  ( const A (type-Ω (pair (type-Truncated-Type BG) pt)) ,
                    is-equiv-const-Id-is-acyclic-Truncated-Type A ac BG pt pt)
                  ( gen))
                ( y))
              ( refl))))
      ( is-inhabited-is-0-acyclic
        ( is-truncated-acyclic-is-truncated-acyclic-succ ac))

  is-0-connected-is-1-acyclic :
    {l : Level} (A : UU l) →
    is-1-acyclic A → is-0-connected A
  is-0-connected-is-1-acyclic A ac =
    is-contr-is-1-acyclic-is-set
      ( type-trunc-Set A)
      ( is-set-type-trunc-Set)
      ( is-truncated-acyclic-succ-type-trunc-is-truncated-acyclic-succ A ac)
```

## References

{{#bibliography}}

## See also

- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
