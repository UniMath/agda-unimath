# The endomorphism rings of abelian groups

```agda
module group-theory.endomorphism-rings-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types

open import group-theory.abelian-groups
open import group-theory.addition-homomorphisms-abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.invertible-elements-monoids
open import group-theory.isomorphisms-abelian-groups
open import group-theory.precategory-of-semigroups

open import ring-theory.invertible-elements-rings
open import ring-theory.rings
```

</details>

## Idea

For any abelian group $A$, the set $\mathrm{hom}(A,A)$ of morphisms of abelian
groups can be equipped with the structure of a ring, where addition is given
pointwise and multiplication is given by composition.

## Definition

### The endomorphism ring on an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  ab-endomorphism-ring-Ab : Ab l
  ab-endomorphism-ring-Ab = ab-hom-Ab A A

  endomorphism-ring-Ab : Ring l
  pr1 endomorphism-ring-Ab = ab-endomorphism-ring-Ab
  pr1 (pr1 (pr2 endomorphism-ring-Ab)) = comp-hom-Ab A A A
  pr2 (pr1 (pr2 endomorphism-ring-Ab)) = associative-comp-hom-Ab A A A A
  pr1 (pr1 (pr2 (pr2 endomorphism-ring-Ab))) = id-hom-Ab A
  pr1 (pr2 (pr1 (pr2 (pr2 endomorphism-ring-Ab)))) =
    left-unit-law-comp-hom-Ab A A
  pr2 (pr2 (pr1 (pr2 (pr2 endomorphism-ring-Ab)))) =
    right-unit-law-comp-hom-Ab A A
  pr1 (pr2 (pr2 (pr2 endomorphism-ring-Ab))) =
    left-distributive-comp-add-hom-Ab A A A
  pr2 (pr2 (pr2 (pr2 endomorphism-ring-Ab))) =
    right-distributive-comp-add-hom-Ab A A A
```

## Properties

### [Isomorphisms](group-theory.isomorphisms-abelian-groups.md) `A ≃ A` are [units](ring-theory.invertible-elements-rings.md) in the endomorphism ring

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-iso-is-invertible-endomorphism-ring-Ab :
    (f : hom-Ab A A) → is-iso-Ab A A f → is-invertible-element-Ring
    ( endomorphism-ring-Ab A) f
  pr1 (is-iso-is-invertible-endomorphism-ring-Ab f f-iso) =
    hom-inv-is-iso-Ab A A f f-iso
  pr1 (pr2 (is-iso-is-invertible-endomorphism-ring-Ab f f-iso)) =
    pr1 (pr2 f-iso)
  pr2 (pr2 (is-iso-is-invertible-endomorphism-ring-Ab f f-iso)) =
    pr2 (pr2 f-iso)
```

### Units in the endomorphism ring are isomorphisms `A ≃ A`

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-invertible-is-iso-endomorphism-ring-Ab :
    (f : hom-Ab A A) → is-invertible-element-Ring (endomorphism-ring-Ab A) f →
    is-iso-Ab A A f
  pr1 (is-invertible-is-iso-endomorphism-ring-Ab f (f-inv , f-inv-is-inv)) =
    f-inv
  pr2 (is-invertible-is-iso-endomorphism-ring-Ab f (f-inv , f-inv-is-inv)) =
    f-inv-is-inv
```
