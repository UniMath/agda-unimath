# Trivial ideals of semirings

```agda
module ring-theory.trivial-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-function-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.left-ideals-semirings
open import ring-theory.right-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
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
```
