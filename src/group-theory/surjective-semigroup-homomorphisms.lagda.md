# Surjective semigroup homomorphisms

```agda
module group-theory.surjective-semigroup-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universe-levels

open import group-theory.full-subsemigroups
open import group-theory.homomorphisms-semigroups
open import group-theory.images-of-semigroup-homomorphisms
open import group-theory.semigroups
```

</details>

A [semigroup homomorphism](group-theory.homomorphisms-semigroups.md) `f : G → H`
is said to be **surjective** if its underlying map is
[surjective](foundation.surjective-maps.md).

## Definition

### Surjective semigroup homomorphisms

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : hom-Semigroup G H)
  where

  is-surjective-prop-hom-Semigroup : Prop (l1 ⊔ l2)
  is-surjective-prop-hom-Semigroup =
    is-surjective-Prop (map-hom-Semigroup G H f)

  is-surjective-hom-Semigroup : UU (l1 ⊔ l2)
  is-surjective-hom-Semigroup = type-Prop is-surjective-prop-hom-Semigroup

  is-prop-is-surjective-hom-Semigroup : is-prop is-surjective-hom-Semigroup
  is-prop-is-surjective-hom-Semigroup =
    is-prop-type-Prop is-surjective-prop-hom-Semigroup
```

## Properties

### A semigroup homomorphism is surjective if and only if its image is the full subsemigroup

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : hom-Semigroup G H)
  where

  is-surjective-is-full-subsemigroup-image-hom-Semigroup :
    is-full-Subsemigroup H (image-hom-Semigroup G H f) →
    is-surjective-hom-Semigroup G H f
  is-surjective-is-full-subsemigroup-image-hom-Semigroup u = u

  is-full-subsemigroup-image-is-surjective-hom-Semigroup :
    is-surjective-hom-Semigroup G H f →
    is-full-Subsemigroup H (image-hom-Semigroup G H f)
  is-full-subsemigroup-image-is-surjective-hom-Semigroup u = u
```
