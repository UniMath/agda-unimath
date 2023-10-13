# Homotopy groups

```agda
module synthetic-homotopy-theory.homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-components
open import foundation.dependent-pair-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.universe-levels

open import group-theory.concrete-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.iterated-loop-spaces
```

</details>

## Idea

The **(abstract) homotopy groups** of a [pointed type](structured-types.pointed-types.md)
`A` are a sequence `i ↦ πᵢ A` where
- `π₀ A` is the [set](foundation.sets.md) of [connected components](foundation.connected-components.md) of `A`, and
- `πᵢ₊₁ A` is  the set `πᵢ ΩA` equipped with the [group structure](group-theory.groups.md) obtained from the [loop space](synthetic-homotopy theory.loop-spaces.md).

For `i ≥ 2`, the `i`-th homotopy group `πᵢ A` of `A` is [abelian](group-theory.abelian-groups.md) by the [Eckmann-Hilton argument](synthetic-homotopy-theory.eckmann-hilton-argument.md).

Alternatively, we can define the **concrete homotopy groups** of a pointed type `A` to be the [sequence](foundation.sequences.md) `ℕ → Concrete-Group`, given by

```text
  i ↦ concrete-group-Pointed-Type (iterated-loop-space i A)
```

However, note that there is an [Obi-wan error](https://www.urbandictionary.com/define.php?term=Obi-wan+error) in this definition: The `0`-th concrete homotopy group corresponds to the first abstract homotopy group.

## Definitions

### The underlying sets of the homotopy groups

```agda
module _
  {l : Level} (n : ℕ) (A : Pointed-Type l)
  where

  set-homotopy-group : Set l
  set-homotopy-group = trunc-Set (type-iterated-loop-space n A)

  type-homotopy-group : UU l
  type-homotopy-group = type-Set set-homotopy-group

  is-set-type-homotopy-group : is-set type-homotopy-group
  is-set-type-homotopy-group = is-set-type-Set set-homotopy-group

  point-homotopy-group : type-homotopy-group
  point-homotopy-group = unit-trunc-Set (point-iterated-loop-space n A)

  pointed-type-homotopy-group : Pointed-Type l
  pr1 pointed-type-homotopy-group = type-homotopy-group
  pr2 pointed-type-homotopy-group = point-homotopy-group
```

### The concrete homotopy groups

```agda
module _
  {l : Level} (n : ℕ) (A : Pointed-Type l)
  where

  concrete-homotopy-group : Concrete-Group l
  concrete-homotopy-group = {!concrete-group-Pointed-Type!}
```
