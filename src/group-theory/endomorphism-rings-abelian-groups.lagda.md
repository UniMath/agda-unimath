# The endomorphism rings of abelian groups

```agda
module group-theory.endomorphism-rings-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.addition-homomorphisms-abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import ring-theory.homomorphisms-rings
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

### Multiplication in a ring is a ring homomorphism in the ring of endomorphism of its underlying abelian additive group

```agda
module _
  {l : Level} (R : Ring l)
  where

  ab-hom-mul-Ring : type-Ring R → type-Ring (endomorphism-ring-Ab (ab-Ring R))
  ab-hom-mul-Ring w =
    ( mul-Ring R w) ,
    ( λ {x y} → left-distributive-mul-add-Ring R w x y)

  preserves-add-ab-hom-mul-Ring :
    {x y : type-Ring R} →
    ab-hom-mul-Ring (add-Ring R x y) ＝
    add-Ring
      ( endomorphism-ring-Ab (ab-Ring R))
      ( ab-hom-mul-Ring x)
      ( ab-hom-mul-Ring y)
  preserves-add-ab-hom-mul-Ring {x} {y} =
    eq-htpy-hom-Ab
      ( ab-Ring R)
      ( ab-Ring R)
      ( right-distributive-mul-add-Ring R x y)

  preserves-mul-ab-hom-mul-Ring :
    {x y : type-Ring R} →
    ab-hom-mul-Ring (mul-Ring R x y) ＝
    mul-Ring
      ( endomorphism-ring-Ab (ab-Ring R))
      ( ab-hom-mul-Ring x)
      ( ab-hom-mul-Ring y)
  preserves-mul-ab-hom-mul-Ring {x} {y} =
    eq-htpy-hom-Ab
      ( ab-Ring R)
      ( ab-Ring R)
      ( associative-mul-Ring R x y)

  preserves-one-ab-hom-Ring :
    ab-hom-mul-Ring (one-Ring R) ＝
    one-Ring (endomorphism-ring-Ab (ab-Ring R))
  preserves-one-ab-hom-Ring =
    eq-htpy-hom-Ab
      ( ab-Ring R)
      ( ab-Ring R)
      ( left-unit-law-mul-Ring R)

  hom-mul-endomorphism-ring-ab-Ring :
    hom-Ring R (endomorphism-ring-Ab (ab-Ring R))
  hom-mul-endomorphism-ring-ab-Ring =
    ( ab-hom-mul-Ring , preserves-add-ab-hom-mul-Ring) ,
    ( preserves-mul-ab-hom-mul-Ring , preserves-one-ab-hom-Ring)
```
