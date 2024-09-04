# Abelian higher groups

```agda
{-# OPTIONS --guardedness #-}

module higher-group-theory.abelian-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.small-types
open import foundation.universe-levels

open import higher-group-theory.equivalences-higher-groups
open import higher-group-theory.higher-groups
open import higher-group-theory.infinitely-deloopable-types
open import higher-group-theory.small-higher-groups

open import structured-types.pointed-equivalences
open import structured-types.pointed-types
open import structured-types.small-pointed-types
```

</details>

## Idea

An {{#concept "abelian" Disambiguation="∞-group"}}, or
{{#concept "commutative" Disambiguation="∞-group"}} ∞-group is a
[higher group](higher-group-theory.higher-groups.md) that is commutative in a
fully coherent way. This may be expressed by saying that the underlying
[pointed type](structured-types.pointed-types.md) is
[infinitely deloopable](higher-group-theory.infinitely-deloopable-types.md).

Abelian ∞-groups thus give an example of another infinitely coherent structure
that is definable in Homotopy Type Theory.

## Definitions

### The predicate of being abelian

```agda
is-abelian-∞-Group : {l : Level} → ∞-Group l → UU (lsuc l)
is-abelian-∞-Group G = infinite-delooping (pointed-type-∞-Group G)
```

## Properties

## External links

- [abelian infinity-group](https://ncatlab.org/nlab/show/abelian+infinity-group)
  at $n$Lab
