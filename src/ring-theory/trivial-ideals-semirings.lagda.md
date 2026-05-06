# Trivial ideals of semirings

```agda
module ring-theory.trivial-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-function-types
open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.left-ideals-semirings
open import ring-theory.poset-of-ideals-semirings
open import ring-theory.poset-of-left-ideals-semirings
open import ring-theory.poset-of-right-ideals-semirings
open import ring-theory.right-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
open import ring-theory.subtractive-ideals-semirings
open import ring-theory.subtractive-left-ideals-semirings
open import ring-theory.subtractive-right-ideals-semirings
```

</details>

## Idea

An [ideal](ring-theory.ideals-semirings.md) `I` of a [semiring](ring-theory.semirings.md) `R` is called {{#concept "trivial" Disambiguation="ideal of a semiring" Agda=is-trivial-ideal-Semiring}} if every element of `I` is `0`.

The (standard) {{#concept "trivial ideal" Disambiguation=semiring Agda=trivial-ideal-Semiring}} is the ideal whose underlying [subset](ring-theory.subsets-semirings.md) is

```text
  { x : R ∣ x ＝ 0 }.
```

## Definitions

### The predicate of being a trivial ideal of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  is-trivial-ideal-Semiring : UU (l1 ⊔ l2)
  is-trivial-ideal-Semiring =
    {x : type-Semiring R} → is-in-ideal-Semiring R I x → is-zero-Semiring R x

  is-prop-is-trivial-ideal-Semiring :
    is-prop is-trivial-ideal-Semiring
  is-prop-is-trivial-ideal-Semiring =
    is-prop-implicit-Π
      ( λ _ → is-prop-function-type (is-set-type-Semiring R _ _))

  is-trivial-prop-ideal-Semiring : Prop (l1 ⊔ l2)
  pr1 is-trivial-prop-ideal-Semiring =
    is-trivial-ideal-Semiring
  pr2 is-trivial-prop-ideal-Semiring =
    is-prop-is-trivial-ideal-Semiring
```

### The predicate of being a trivial left ideal of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  is-trivial-left-ideal-Semiring : UU (l1 ⊔ l2)
  is-trivial-left-ideal-Semiring =
    {x : type-Semiring R} →
    is-in-left-ideal-Semiring R I x → is-zero-Semiring R x

  is-prop-is-trivial-left-ideal-Semiring :
    is-prop is-trivial-left-ideal-Semiring
  is-prop-is-trivial-left-ideal-Semiring =
    is-prop-implicit-Π
      ( λ _ → is-prop-function-type (is-set-type-Semiring R _ _))

  is-trivial-prop-left-ideal-Semiring : Prop (l1 ⊔ l2)
  pr1 is-trivial-prop-left-ideal-Semiring =
    is-trivial-left-ideal-Semiring
  pr2 is-trivial-prop-left-ideal-Semiring =
    is-prop-is-trivial-left-ideal-Semiring
```

### The predicate of being a trivial right ideal of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  is-trivial-right-ideal-Semiring : UU (l1 ⊔ l2)
  is-trivial-right-ideal-Semiring =
    {x : type-Semiring R} →
    is-in-right-ideal-Semiring R I x → is-zero-Semiring R x

  is-prop-is-trivial-right-ideal-Semiring :
    is-prop is-trivial-right-ideal-Semiring
  is-prop-is-trivial-right-ideal-Semiring =
    is-prop-implicit-Π
      ( λ _ → is-prop-function-type (is-set-type-Semiring R _ _))

  is-trivial-prop-right-ideal-Semiring : Prop (l1 ⊔ l2)
  pr1 is-trivial-prop-right-ideal-Semiring =
    is-trivial-right-ideal-Semiring
  pr2 is-trivial-prop-right-ideal-Semiring =
    is-prop-is-trivial-right-ideal-Semiring
```

### The standard trivial ideal of a semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  subset-trivial-ideal-Semiring : subset-Semiring l1 R
  subset-trivial-ideal-Semiring x = Id-Prop (set-Semiring R) x (zero-Semiring R)

  is-in-trivial-ideal-Semiring : type-Semiring R → UU l1
  is-in-trivial-ideal-Semiring =
    is-in-subset-Semiring R subset-trivial-ideal-Semiring

  is-prop-is-in-trivial-ideal-Semiring :
    (x : type-Semiring R) → is-prop (is-in-trivial-ideal-Semiring x)
  is-prop-is-in-trivial-ideal-Semiring =
    is-prop-is-in-subset-Semiring R subset-trivial-ideal-Semiring

  type-trivial-ideal-Semiring :
    UU l1
  type-trivial-ideal-Semiring =
    type-subset-Semiring R subset-trivial-ideal-Semiring

  inclusion-trivial-ideal-Semiring :
    type-trivial-ideal-Semiring → type-Semiring R
  inclusion-trivial-ideal-Semiring =
    inclusion-subset-Semiring R subset-trivial-ideal-Semiring

  ap-inclusion-trivial-ideal-Semiring :
    (x y : type-trivial-ideal-Semiring) → x ＝ y →
    inclusion-trivial-ideal-Semiring x ＝ inclusion-trivial-ideal-Semiring y
  ap-inclusion-trivial-ideal-Semiring =
    ap-inclusion-subset-Semiring R subset-trivial-ideal-Semiring

  is-in-trivial-ideal-inclusion-trivial-ideal-Semiring :
    (x : type-trivial-ideal-Semiring) →
    is-in-trivial-ideal-Semiring (inclusion-trivial-ideal-Semiring x)
  is-in-trivial-ideal-inclusion-trivial-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R subset-trivial-ideal-Semiring

  is-closed-under-eq-trivial-ideal-Semiring :
    {x y : type-Semiring R} → is-in-trivial-ideal-Semiring x →
    x ＝ y → is-in-trivial-ideal-Semiring y
  is-closed-under-eq-trivial-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R subset-trivial-ideal-Semiring

  is-closed-under-eq-trivial-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-trivial-ideal-Semiring y →
    x ＝ y → is-in-trivial-ideal-Semiring x
  is-closed-under-eq-trivial-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R subset-trivial-ideal-Semiring

  contains-zero-trivial-ideal-Semiring :
    contains-zero-subset-Semiring R subset-trivial-ideal-Semiring
  contains-zero-trivial-ideal-Semiring = refl

  is-closed-under-addition-trivial-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-trivial-ideal-Semiring
  is-closed-under-addition-trivial-ideal-Semiring refl refl =
    left-unit-law-add-Semiring R _

  is-additive-submonoid-trivial-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R subset-trivial-ideal-Semiring
  pr1 is-additive-submonoid-trivial-ideal-Semiring =
    contains-zero-trivial-ideal-Semiring
  pr2 is-additive-submonoid-trivial-ideal-Semiring =
    is-closed-under-addition-trivial-ideal-Semiring

  is-closed-under-two-sided-multiplication-trivial-ideal-Semiring :
    is-closed-under-two-sided-multiplication-subset-Semiring R
      subset-trivial-ideal-Semiring
  is-closed-under-two-sided-multiplication-trivial-ideal-Semiring refl =
    ap (mul-Semiring' R _) (right-zero-law-mul-Semiring R _) ∙
    left-zero-law-mul-Semiring R _

  is-closed-under-left-multiplication-trivial-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-trivial-ideal-Semiring
  is-closed-under-left-multiplication-trivial-ideal-Semiring refl =
    right-zero-law-mul-Semiring R _

  is-closed-under-right-multiplication-trivial-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-trivial-ideal-Semiring
  is-closed-under-right-multiplication-trivial-ideal-Semiring refl =
    left-zero-law-mul-Semiring R _

  is-closed-under-multiplication-trivial-ideal-Semiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-trivial-ideal-Semiring
  is-closed-under-multiplication-trivial-ideal-Semiring refl refl =
    left-zero-law-mul-Semiring R _

  is-left-ideal-trivial-ideal-Semiring :
    is-left-ideal-subset-Semiring R subset-trivial-ideal-Semiring
  pr1 is-left-ideal-trivial-ideal-Semiring =
    is-additive-submonoid-trivial-ideal-Semiring
  pr2 is-left-ideal-trivial-ideal-Semiring =
    is-closed-under-left-multiplication-trivial-ideal-Semiring

  trivial-left-ideal-Semiring : left-ideal-Semiring l1 R
  pr1 trivial-left-ideal-Semiring = subset-trivial-ideal-Semiring
  pr2 trivial-left-ideal-Semiring = is-left-ideal-trivial-ideal-Semiring

  is-right-ideal-trivial-ideal-Semiring :
    is-right-ideal-subset-Semiring R subset-trivial-ideal-Semiring
  pr1 is-right-ideal-trivial-ideal-Semiring =
    is-additive-submonoid-trivial-ideal-Semiring
  pr2 is-right-ideal-trivial-ideal-Semiring =
    is-closed-under-right-multiplication-trivial-ideal-Semiring

  trivial-right-ideal-Semiring : right-ideal-Semiring l1 R
  pr1 trivial-right-ideal-Semiring = subset-trivial-ideal-Semiring
  pr2 trivial-right-ideal-Semiring = is-right-ideal-trivial-ideal-Semiring

  is-ideal-trivial-ideal-Semiring :
    is-ideal-subset-Semiring R subset-trivial-ideal-Semiring
  pr1 is-ideal-trivial-ideal-Semiring =
    is-additive-submonoid-trivial-ideal-Semiring
  pr2 is-ideal-trivial-ideal-Semiring =
    is-closed-under-two-sided-multiplication-trivial-ideal-Semiring

  trivial-ideal-Semiring : ideal-Semiring l1 R
  pr1 trivial-ideal-Semiring = subset-trivial-ideal-Semiring
  pr2 trivial-ideal-Semiring = is-ideal-trivial-ideal-Semiring

  is-trivial-trivial-ideal-Semiring :
    is-trivial-ideal-Semiring R trivial-ideal-Semiring
  is-trivial-trivial-ideal-Semiring H = H

  is-trivial-trivial-left-ideal-Semiring :
    is-trivial-left-ideal-Semiring R trivial-left-ideal-Semiring
  is-trivial-trivial-left-ideal-Semiring H = H

  is-trivial-trivial-right-ideal-Semiring :
    is-trivial-right-ideal-Semiring R trivial-right-ideal-Semiring
  is-trivial-trivial-right-ideal-Semiring H = H
```

## Properties

### Any trivial ideal is subtractive

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  is-subtractive-is-trivial-ideal-Semiring :
    is-trivial-ideal-Semiring R I → is-subtractive-ideal-Semiring R I
  is-subtractive-is-trivial-ideal-Semiring H u v =
    is-closed-under-eq-ideal-Semiring R I v
      ( ap (add-Semiring' R _) (H u) ∙ left-unit-law-add-Semiring R _)

module _
  {l1 : Level} (R : Semiring l1)
  where

  is-subtractive-trivial-ideal-Semiring :
    is-subtractive-ideal-Semiring R (trivial-ideal-Semiring R)
  is-subtractive-trivial-ideal-Semiring =
    is-subtractive-is-trivial-ideal-Semiring R
      ( trivial-ideal-Semiring R)
      ( is-trivial-trivial-ideal-Semiring R)

  trivial-subtractive-ideal-Semiring :
    subtractive-ideal-Semiring l1 R
  pr1 trivial-subtractive-ideal-Semiring =
    trivial-ideal-Semiring R
  pr2 trivial-subtractive-ideal-Semiring =
    is-subtractive-trivial-ideal-Semiring

module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  is-subtractive-is-trivial-left-ideal-Semiring :
    is-trivial-left-ideal-Semiring R I →
    is-subtractive-left-ideal-Semiring R I
  is-subtractive-is-trivial-left-ideal-Semiring H u v =
    is-closed-under-eq-left-ideal-Semiring R I v
      ( ap (add-Semiring' R _) (H u) ∙ left-unit-law-add-Semiring R _)

module _
  {l1 : Level} (R : Semiring l1)
  where

  is-subtractive-trivial-left-ideal-Semiring :
    is-subtractive-left-ideal-Semiring R (trivial-left-ideal-Semiring R)
  is-subtractive-trivial-left-ideal-Semiring =
    is-subtractive-is-trivial-left-ideal-Semiring R
      ( trivial-left-ideal-Semiring R)
      ( is-trivial-trivial-left-ideal-Semiring R)

  trivial-subtractive-left-ideal-Semiring :
    subtractive-left-ideal-Semiring l1 R
  pr1 trivial-subtractive-left-ideal-Semiring =
    trivial-left-ideal-Semiring R
  pr2 trivial-subtractive-left-ideal-Semiring =
    is-subtractive-trivial-left-ideal-Semiring

module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  is-subtractive-is-trivial-right-ideal-Semiring :
    is-trivial-right-ideal-Semiring R I →
    is-subtractive-right-ideal-Semiring R I
  is-subtractive-is-trivial-right-ideal-Semiring H u v =
    is-closed-under-eq-right-ideal-Semiring R I v
      ( ap (add-Semiring' R _) (H u) ∙ left-unit-law-add-Semiring R _)

module _
  {l1 : Level} (R : Semiring l1)
  where

  is-subtractive-trivial-right-ideal-Semiring :
    is-subtractive-right-ideal-Semiring R (trivial-right-ideal-Semiring R)
  is-subtractive-trivial-right-ideal-Semiring =
    is-subtractive-is-trivial-right-ideal-Semiring R
      ( trivial-right-ideal-Semiring R)
      ( is-trivial-trivial-right-ideal-Semiring R)

  trivial-subtractive-right-ideal-Semiring :
    subtractive-right-ideal-Semiring l1 R
  pr1 trivial-subtractive-right-ideal-Semiring =
    trivial-right-ideal-Semiring R
  pr2 trivial-subtractive-right-ideal-Semiring =
    is-subtractive-trivial-right-ideal-Semiring
```

### Any ideal contained in a trivial ideal is trivial

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (I : ideal-Semiring l2 R) (J : ideal-Semiring l3 R)
  where

  is-trivial-leq-ideal-Semiring :
    is-trivial-ideal-Semiring R J →
    leq-ideal-Semiring R I J →
    is-trivial-ideal-Semiring R I
  is-trivial-leq-ideal-Semiring H K u = H (K _ u)

module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (I : left-ideal-Semiring l2 R) (J : left-ideal-Semiring l3 R)
  where

  is-trivial-leq-left-ideal-Semiring :
    is-trivial-left-ideal-Semiring R J →
    leq-left-ideal-Semiring R I J →
    is-trivial-left-ideal-Semiring R I
  is-trivial-leq-left-ideal-Semiring H K u = H (K _ u)

module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (I : right-ideal-Semiring l2 R) (J : right-ideal-Semiring l3 R)
  where

  is-trivial-leq-right-ideal-Semiring :
    is-trivial-right-ideal-Semiring R J →
    leq-right-ideal-Semiring R I J →
    is-trivial-right-ideal-Semiring R I
  is-trivial-leq-right-ideal-Semiring H K u = H (K _ u)
```

### Any trivial ideal is contained in any other ideal

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (I : ideal-Semiring l2 R) (J : ideal-Semiring l3 R)
  where

  leq-is-trivial-ideal-Semiring :
    is-trivial-ideal-Semiring R I →
    leq-ideal-Semiring R I J
  leq-is-trivial-ideal-Semiring H x u =
    is-closed-under-eq-ideal-Semiring' R J
      ( contains-zero-ideal-Semiring R J)
      ( H u)

module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (I : left-ideal-Semiring l2 R) (J : left-ideal-Semiring l3 R)
  where

  leq-is-trivial-left-ideal-Semiring :
    is-trivial-left-ideal-Semiring R I →
    leq-left-ideal-Semiring R I J
  leq-is-trivial-left-ideal-Semiring H x u =
    is-closed-under-eq-left-ideal-Semiring' R J
      ( contains-zero-left-ideal-Semiring R J)
      ( H u)

module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (I : right-ideal-Semiring l2 R) (J : right-ideal-Semiring l3 R)
  where

  leq-is-trivial-right-ideal-Semiring :
    is-trivial-right-ideal-Semiring R I →
    leq-right-ideal-Semiring R I J
  leq-is-trivial-right-ideal-Semiring H x u =
    is-closed-under-eq-right-ideal-Semiring' R J
      ( contains-zero-right-ideal-Semiring R J)
      ( H u)
```
