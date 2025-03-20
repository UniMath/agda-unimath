# Deloopable types

```agda
open import foundation.function-extensionality-axiom

module
  higher-group-theory.deloopable-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.small-types funext
open import foundation.universe-levels

open import higher-group-theory.equivalences-higher-groups funext
open import higher-group-theory.higher-groups funext
open import higher-group-theory.small-higher-groups funext

open import structured-types.pointed-equivalences funext
open import structured-types.pointed-types
open import structured-types.small-pointed-types funext
```

</details>

## Idea

Consider a [pointed type](structured-types.pointed-types.md) `X` and a pointed
[connected](foundation.0-connected-types.md) type `Y`. We say that `Y` is a
{{#concept "delooping" Disambiguation="pointed type" Agda=is-delooping}} of `X`
if we have a [pointed equivalence](structured-types.pointed-equivalences.md)

```text
  X ≃∗ Ω Y.
```

Recall that a pointed connected type is an
[∞-group](higher-group-theory.higher-groups.md). An ∞-group `G` is therefore a
delooping of `X` if its underlying pointed type is pointed equivalent to `X`. A
{{#concept "delooping" Disambiguation="pointed type" Agda=delooping}} of `X`
therefore consist of an ∞-group `G` and a pointed equivalence

```text
  X ≃∗ type-∞-Group G
```

In other words, the type of deloopings of `X` is defined to be

```text
  delooping X := Σ (Y : ∞-Group), X ≃∗ Ω Y.
```

### Relation to higher group structures

A delooping of a pointed type `X` is, in quite a literal way, an
{{#concept "∞-group structure" Agda=delooping}} on `X`. In other words, the type
`delooping X` is the type of ∞-group structures on `X`. Indeed, the type of all
pointed types equipped with deloopings is
[equivalent](foundation-core.equivalences.md) to the type of ∞-groups, by
extensionality of the type of pointed types.

Being deloopable is therefore a [structure](foundation.structure.md), and
usually not a [property](foundation-core.propositions.md). If there are multiple
distinct ways to equip a pointed type `X` with the structure of an ∞-group, or
even with the structure of a [group](group-theory.groups.md), then the type of
deloopings of `X` will not be a proposition. For instance, the
[standard `4`-element type](univalent-combinatorics.standard-finite-types.md)
`Fin 4` is deloopable in multiple distinct ways, by equipping it with the
[cyclic group structure](group-theory.cyclic-groups.md) of `ℤ₄` or by equipping
it with the group structure of `ℤ₂ × ℤ₂`.

### Universe levels in the definition of being deloopable

Note that there is a small question about universe levels in the definition of
being a deloopable type. We say that a type is deloopable in a universe `𝒰` if
there is an ∞-group `Y` in the universe `𝒰` that is a delooping of `X`. However,
by the [type theoretic replacement principle](foundation.replacement.md) it
follows that any delooping of `X` is always [small](foundation.small-types.md)
with respect to the universe of `X` itself. Therefore we simply say that `X` is
deloopable, i.e., without reference to any universes, if `X` is deloopable in
its own universe.

## Definitions

### The predicate of being a delooping

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1)
  where

  is-delooping : (G : ∞-Group l2) → UU (l1 ⊔ l2)
  is-delooping G = X ≃∗ pointed-type-∞-Group G
```

### The type of deloopings of a pointed type, in a given universe

```agda
module _
  {l1 : Level} (X : Pointed-Type l1)
  where

  delooping-Level : (l : Level) → UU (l1 ⊔ lsuc l)
  delooping-Level l = Σ (∞-Group l) (is-delooping X)

  module _
    {l : Level} (Y : delooping-Level l)
    where

    ∞-group-delooping-Level : ∞-Group l
    ∞-group-delooping-Level = pr1 Y

    classifying-pointed-type-∞-group-delooping-Level : Pointed-Type l
    classifying-pointed-type-∞-group-delooping-Level =
      classifying-pointed-type-∞-Group ∞-group-delooping-Level

    classifying-type-∞-group-delooping-Level : UU l
    classifying-type-∞-group-delooping-Level =
      classifying-type-∞-Group ∞-group-delooping-Level

    is-delooping-delooping-Level : is-delooping X ∞-group-delooping-Level
    is-delooping-delooping-Level = pr2 Y

    equiv-is-delooping-delooping-Level :
      type-Pointed-Type X ≃ type-∞-Group ∞-group-delooping-Level
    equiv-is-delooping-delooping-Level =
      equiv-pointed-equiv is-delooping-delooping-Level
```

### The type of deloopings of a pointed type

```agda
module _
  {l1 : Level} (X : Pointed-Type l1)
  where

  delooping : UU (lsuc l1)
  delooping = delooping-Level X l1
```

## Properties

### The delooping of a pointed type in a universe `𝒰` is a `𝒰`-small ∞-group

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (H : delooping-Level X l2)
  where

  abstract
    is-small-∞-group-delooping-Level :
      is-small-∞-Group l1 (∞-group-delooping-Level X H)
    pr1 is-small-∞-group-delooping-Level = type-Pointed-Type X
    pr2 is-small-∞-group-delooping-Level =
      inv-equiv (equiv-is-delooping-delooping-Level X H)

  abstract
    is-small-classifying-type-∞-group-delooping-Level :
      is-small l1 (classifying-type-∞-group-delooping-Level X H)
    is-small-classifying-type-∞-group-delooping-Level =
      is-small-classifying-type-is-small-∞-Group
        ( ∞-group-delooping-Level X H)
        ( is-small-∞-group-delooping-Level)

  abstract
    is-pointed-small-classifying-pointed-type-∞-group-delooping-Level :
      is-pointed-small-Pointed-Type l1
        ( classifying-pointed-type-∞-group-delooping-Level X H)
    is-pointed-small-classifying-pointed-type-∞-group-delooping-Level =
      is-pointed-small-is-small-Pointed-Type
        ( classifying-pointed-type-∞-group-delooping-Level X H)
        ( is-small-classifying-type-∞-group-delooping-Level)
```

### If a pointed type in universe `𝒰 l1` is deloopable in any universe, then it is deloopable in `𝒰 l1`

Suppose `X` is a pointed type of universe level `l1`, which is deloopable in
universe level `l2`. Then there is an ∞-group `H` of universe level `l2`
equipped with a pointed equivalence

```text
  X ≃∗ type-∞-Group H.
```

This implies that the ∞-group `H` is `l1`-small, because its underlying type is
equivalent to the underlying type of `X`. Hence there is an ∞-group `K` equipped
with an
[equivalence of ∞-groups](higher-group-theory.equivalences-higher-groups.md)

```text
  H ≃ K.
```

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (H : delooping-Level X l2)
  where

  ∞-group-delooping-delooping-level : ∞-Group l1
  ∞-group-delooping-delooping-level =
    ∞-group-is-small-∞-Group
      ( ∞-group-delooping-Level X H)
      ( type-Pointed-Type X ,
        equiv-inv-pointed-equiv (is-delooping-delooping-Level X H))

  is-delooping-delooping-delooping-Level :
    is-delooping X ∞-group-delooping-delooping-level
  is-delooping-delooping-delooping-Level =
    comp-pointed-equiv
      ( pointed-equiv-equiv-∞-Group
        ( ∞-group-delooping-Level X H)
        ( ∞-group-delooping-delooping-level)
        ( equiv-∞-group-is-small-∞-Group
          ( ∞-group-delooping-Level X H)
          ( type-Pointed-Type X ,
            equiv-inv-pointed-equiv (is-delooping-delooping-Level X H))))
      ( is-delooping-delooping-Level X H)

  delooping-delooping-Level : delooping X
  pr1 delooping-delooping-Level = ∞-group-delooping-delooping-level
  pr2 delooping-delooping-Level = is-delooping-delooping-delooping-Level
```

## See also

- [Deloopable H-spaces](higher-group-theory.deloopable-h-spaces.md)
- [Deloopable groups](higher-group-theory.deloopable-groups.md)
