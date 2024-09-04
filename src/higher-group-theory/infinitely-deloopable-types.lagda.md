# Infinitely deloopable types

```agda
{-# OPTIONS --guardedness #-}

module higher-group-theory.infinitely-deloopable-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.small-types
open import foundation.universe-levels

open import higher-group-theory.deloopable-types
open import higher-group-theory.equivalences-higher-groups
open import higher-group-theory.higher-groups
open import higher-group-theory.small-higher-groups

open import structured-types.pointed-equivalences
open import structured-types.pointed-types
open import structured-types.small-pointed-types
```

</details>

## Idea

A [pointed type](structured-types.pointed-types.md) `X` is said to be
{{#concept "infinitely deloopable" Disambiguation="pointed type" Agda=infinite-delooping}}
if it is
[$n$-deloopable](higher-group-theory.iterated-deloopings-of-pointed-types.md)
for all $n$, or equivalently, if it is
[deloopable](higher-group-theory.deloopable-types.md) and coinductively its
delooping is also infinitely deloopable.

### Relation to commutative higher group structures

An infinite delooping of a pointed type `X` is, in a specific sense, a
{{#concept "commutative ∞-group structure" Agda=infinite-delooping}} on `X`. In
other words, the type `infinite-delooping X` is the type of commutative ∞-group
structures on `X`.

Being infinitely deloopable is therefore a [structure](foundation.structure.md),
and usually not a [property](foundation-core.propositions.md). If there are
multiple distinct ways to equip a pointed type `X` with the structure of a
commutative ∞-group, or even with the structure of an
[abelian group](group-theory.abelian-groups.md), then the type of infinite
deloopings of `X` will not be a proposition. For instance, the
[standard `4`-element type](univalent-combinatorics.standard-finite-types.md)
`Fin 4` is infinitely deloopable in multiple distinct ways, by equipping it with
the [cyclic group structure](group-theory.cyclic-groups.md) of `ℤ₄` or by
equipping it with the group structure of `ℤ₂ × ℤ₂`.

## Definitions

### The type of infinite deloopings of a pointed type

```agda
record
  infinite-delooping
  {l : Level} (X : Pointed-Type l) : UU (lsuc l)
  where
  coinductive
  field
    ∞-group-infinite-delooping : ∞-Group l

    is-delooping-infinite-delooping :
      is-delooping X ∞-group-infinite-delooping

  classifying-pointed-type-infinite-delooping : Pointed-Type l
  classifying-pointed-type-infinite-delooping =
    classifying-pointed-type-∞-Group ∞-group-infinite-delooping

  classifying-type-infinite-delooping : UU l
  classifying-type-infinite-delooping =
    classifying-type-∞-Group ∞-group-infinite-delooping

  equiv-is-delooping-infinite-delooping :
    type-Pointed-Type X ≃ type-∞-Group ∞-group-infinite-delooping
  equiv-is-delooping-infinite-delooping =
    equiv-pointed-equiv is-delooping-infinite-delooping

  field
    infinite-delooping-∞-group-infinite-delooping :
      infinite-delooping classifying-pointed-type-infinite-delooping

open infinite-delooping public
```

## External links

- [infinite loop space](https://ncatlab.org/nlab/show/infinite+loop+space) at
  $n$Lab
