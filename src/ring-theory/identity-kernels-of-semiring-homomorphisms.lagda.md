# Identity kernels of semiring homomorphisms

```agda
module ring-theory.identity-kernels-of-semiring-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.identity-kernels-homomorphisms-monoids
open import group-theory.submonoids

open import ring-theory.homomorphisms-semirings
open import ring-theory.ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

The
{{#concept "kernel" Disambiguation="of a semiring homomorphism" Agda=kernel-hom-Semiring}}
of a [semiring homomorphism](ring-theory.homomorphisms-semirings.md) `f : R → S` is the
[ideal](ring-theory.ideals-semirings.md) of `R` consisting of all elements `x : R`
equipped with an [identification](foundation-core.identity-types.md) `f x ＝ 0`.

## Definitions

### The kernel of a semiring homomorphism

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  submonoid-kernel-hom-Semiring :
    Submonoid l2 (additive-monoid-Semiring R)
  submonoid-kernel-hom-Semiring = ?
{-
  subgroup-kernel-hom-Group
      ( group-Semiring R)
      ( group-Semiring S)
      ( hom-group-hom-Semiring R S f) -}

  subset-kernel-hom-Semiring : subset-Semiring l2 R
  subset-kernel-hom-Semiring =
    subset-Subgroup-Ab (ab-Semiring R) subgroup-kernel-hom-Semiring

  contains-zero-kernel-hom-Semiring :
    contains-zero-subset-Semiring R subset-kernel-hom-Semiring
  contains-zero-kernel-hom-Semiring =
    contains-zero-Subgroup-Ab (ab-Semiring R) subgroup-kernel-hom-Semiring

  is-closed-under-addition-kernel-hom-Semiring :
    is-closed-under-addition-subset-Semiring R subset-kernel-hom-Semiring
  is-closed-under-addition-kernel-hom-Semiring =
    is-closed-under-addition-Subgroup-Ab (ab-Semiring R) subgroup-kernel-hom-Semiring

  is-closed-under-negatives-kernel-hom-Semiring :
    is-closed-under-negatives-subset-Semiring R subset-kernel-hom-Semiring
  is-closed-under-negatives-kernel-hom-Semiring =
    is-closed-under-negatives-Subgroup-Ab (ab-Semiring R) subgroup-kernel-hom-Semiring

  is-additive-subgroup-kernel-hom-Semiring :
    is-additive-subgroup-subset-Semiring R subset-kernel-hom-Semiring
  pr1 is-additive-subgroup-kernel-hom-Semiring =
    contains-zero-kernel-hom-Semiring
  pr1 (pr2 is-additive-subgroup-kernel-hom-Semiring) =
    is-closed-under-addition-kernel-hom-Semiring
  pr2 (pr2 is-additive-subgroup-kernel-hom-Semiring) =
    is-closed-under-negatives-kernel-hom-Semiring

  is-closed-under-left-multiplication-kernel-hom-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R subset-kernel-hom-Semiring
  is-closed-under-left-multiplication-kernel-hom-Semiring H =
    ( inv (right-zero-law-mul-Semiring S _)) ∙
    ( ap (mul-Semiring S _) H) ∙
    ( inv (preserves-mul-hom-Semiring R S f))

  is-closed-under-right-multiplication-kernel-hom-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R subset-kernel-hom-Semiring
  is-closed-under-right-multiplication-kernel-hom-Semiring H =
    ( inv (left-zero-law-mul-Semiring S _)) ∙
    ( ap (mul-Semiring' S _) H) ∙
    ( inv (preserves-mul-hom-Semiring R S f))

  kernel-hom-Semiring : ideal-Semiring l2 R
  pr1 kernel-hom-Semiring =
    subset-kernel-hom-Semiring
  pr1 (pr2 kernel-hom-Semiring) =
    is-additive-subgroup-kernel-hom-Semiring
  pr1 (pr2 (pr2 kernel-hom-Semiring)) =
    is-closed-under-left-multiplication-kernel-hom-Semiring
  pr2 (pr2 (pr2 kernel-hom-Semiring)) =
    is-closed-under-right-multiplication-kernel-hom-Semiring
```
