# Kernels of ring homomorphisms

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.kernels-of-ring-homomorphisms
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import group-theory.kernels-homomorphisms-groups funext univalence truncations
open import group-theory.subgroups-abelian-groups funext univalence truncations

open import ring-theory.homomorphisms-rings funext univalence truncations
open import ring-theory.ideals-rings funext univalence truncations
open import ring-theory.rings funext univalence truncations
open import ring-theory.subsets-rings funext univalence truncations
```

</details>

## Idea

The **kernel** of a [ring homomorphism](ring-theory.homomorphisms-rings.md)
`f : R → S` is the [ideal](ring-theory.ideals-rings.md) of `R` consisting of all
elements `x : R` equipped with an identification `f x ＝ 0`.

## Definitions

### The kernel of a ring homomorphism

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  subgroup-kernel-hom-Ring : Subgroup-Ab l2 (ab-Ring R)
  subgroup-kernel-hom-Ring =
    subgroup-kernel-hom-Group
      ( group-Ring R)
      ( group-Ring S)
      ( hom-group-hom-Ring R S f)

  subset-kernel-hom-Ring : subset-Ring l2 R
  subset-kernel-hom-Ring =
    subset-Subgroup-Ab (ab-Ring R) subgroup-kernel-hom-Ring

  contains-zero-kernel-hom-Ring :
    contains-zero-subset-Ring R subset-kernel-hom-Ring
  contains-zero-kernel-hom-Ring =
    contains-zero-Subgroup-Ab (ab-Ring R) subgroup-kernel-hom-Ring

  is-closed-under-addition-kernel-hom-Ring :
    is-closed-under-addition-subset-Ring R subset-kernel-hom-Ring
  is-closed-under-addition-kernel-hom-Ring =
    is-closed-under-addition-Subgroup-Ab (ab-Ring R) subgroup-kernel-hom-Ring

  is-closed-under-negatives-kernel-hom-Ring :
    is-closed-under-negatives-subset-Ring R subset-kernel-hom-Ring
  is-closed-under-negatives-kernel-hom-Ring =
    is-closed-under-negatives-Subgroup-Ab (ab-Ring R) subgroup-kernel-hom-Ring

  is-additive-subgroup-kernel-hom-Ring :
    is-additive-subgroup-subset-Ring R subset-kernel-hom-Ring
  pr1 is-additive-subgroup-kernel-hom-Ring =
    contains-zero-kernel-hom-Ring
  pr1 (pr2 is-additive-subgroup-kernel-hom-Ring) =
    is-closed-under-addition-kernel-hom-Ring
  pr2 (pr2 is-additive-subgroup-kernel-hom-Ring) =
    is-closed-under-negatives-kernel-hom-Ring

  is-closed-under-left-multiplication-kernel-hom-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-kernel-hom-Ring
  is-closed-under-left-multiplication-kernel-hom-Ring x y H =
    ( inv (right-zero-law-mul-Ring S _)) ∙
    ( ap (mul-Ring S _) H) ∙
    ( inv (preserves-mul-hom-Ring R S f))

  is-closed-under-right-multiplication-kernel-hom-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-kernel-hom-Ring
  is-closed-under-right-multiplication-kernel-hom-Ring x y H =
    ( inv (left-zero-law-mul-Ring S _)) ∙
    ( ap (mul-Ring' S _) H) ∙
    ( inv (preserves-mul-hom-Ring R S f))

  kernel-hom-Ring : ideal-Ring l2 R
  pr1 kernel-hom-Ring =
    subset-kernel-hom-Ring
  pr1 (pr2 kernel-hom-Ring) =
    is-additive-subgroup-kernel-hom-Ring
  pr1 (pr2 (pr2 kernel-hom-Ring)) =
    is-closed-under-left-multiplication-kernel-hom-Ring
  pr2 (pr2 (pr2 kernel-hom-Ring)) =
    is-closed-under-right-multiplication-kernel-hom-Ring
```
