# Surjective semigroup homomorphisms

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.surjective-semigroup-homomorphisms
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.surjective-maps funext univalence truncations
open import foundation.universe-levels

open import group-theory.full-subsemigroups funext univalence truncations
open import group-theory.homomorphisms-semigroups funext univalence truncations
open import group-theory.images-of-semigroup-homomorphisms funext univalence truncations
open import group-theory.semigroups funext univalence
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
