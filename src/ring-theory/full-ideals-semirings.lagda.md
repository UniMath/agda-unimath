# Full ideals of semirings

```agda
module ring-theory.full-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.full-subtypes
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.raising-universe-levels-unit-type
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.top-elements-large-posets

open import ring-theory.ideals-semirings
open import ring-theory.left-ideals-semirings
open import ring-theory.poset-of-ideals-semirings
open import ring-theory.right-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

A
{{#concept "full ideal" Disambiguation="of a semiring" Agda=is-full-ideal-Semiring Agda=full-ideal-Semiring}}
of a [semiring](ring-theory.semirings.md) `R` is an [ideal](ring-theory.ideals-semirings.md)
that contains every element of `R`.

## Definitions

### The predicate of being a full ideal

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  is-full-ideal-Semiring-Prop : Prop (l1 ⊔ l2)
  is-full-ideal-Semiring-Prop =
    Π-Prop (type-Semiring R) (λ x → subset-ideal-Semiring R I x)

  is-full-ideal-Semiring : UU (l1 ⊔ l2)
  is-full-ideal-Semiring = type-Prop is-full-ideal-Semiring-Prop

  is-prop-is-full-ideal-Semiring : is-prop is-full-ideal-Semiring
  is-prop-is-full-ideal-Semiring =
    is-prop-type-Prop is-full-ideal-Semiring-Prop
```

### The (standard) full ideal

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  subset-full-ideal-Semiring : subset-Semiring lzero R
  subset-full-ideal-Semiring = full-subtype lzero (type-Semiring R)

  is-in-full-ideal-Semiring : type-Semiring R → UU lzero
  is-in-full-ideal-Semiring = is-in-subtype subset-full-ideal-Semiring

  contains-zero-full-ideal-Semiring :
    contains-zero-subset-Semiring R subset-full-ideal-Semiring
  contains-zero-full-ideal-Semiring =
    raise-star {lzero}

  is-closed-under-addition-full-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-full-ideal-Semiring
  is-closed-under-addition-full-ideal-Semiring H K =
    raise-star {lzero}

  is-additive-submonoid-full-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R subset-full-ideal-Semiring
  pr1 is-additive-submonoid-full-ideal-Semiring =
    contains-zero-full-ideal-Semiring
  pr2 is-additive-submonoid-full-ideal-Semiring {x} {y} =
    is-closed-under-addition-full-ideal-Semiring {x} {y}

  is-closed-under-left-multiplication-full-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-full-ideal-Semiring
  is-closed-under-left-multiplication-full-ideal-Semiring H =
    raise-star

  is-closed-under-right-multiplication-full-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-full-ideal-Semiring
  is-closed-under-right-multiplication-full-ideal-Semiring H =
    raise-star

  is-closed-under-two-sided-multiplication-full-ideal-Semiring :
    is-closed-under-two-sided-multiplication-subset-Semiring R
      subset-full-ideal-Semiring
  is-closed-under-two-sided-multiplication-full-ideal-Semiring H =
    raise-star

  is-left-ideal-full-ideal-Semiring :
    is-left-ideal-subset-Semiring R subset-full-ideal-Semiring
  pr1 is-left-ideal-full-ideal-Semiring =
    is-additive-submonoid-full-ideal-Semiring
  pr2 is-left-ideal-full-ideal-Semiring {x} {y} =
    is-closed-under-left-multiplication-full-ideal-Semiring {x} {y}

  full-left-ideal-Semiring : left-ideal-Semiring lzero R
  pr1 full-left-ideal-Semiring = subset-full-ideal-Semiring
  pr2 full-left-ideal-Semiring = is-left-ideal-full-ideal-Semiring

  is-right-ideal-full-ideal-Semiring :
    is-right-ideal-subset-Semiring R subset-full-ideal-Semiring
  pr1 is-right-ideal-full-ideal-Semiring =
    is-additive-submonoid-full-ideal-Semiring
  pr2 is-right-ideal-full-ideal-Semiring {x} {y} =
    is-closed-under-right-multiplication-full-ideal-Semiring {x} {y}

  full-right-ideal-Semiring : right-ideal-Semiring lzero R
  pr1 full-right-ideal-Semiring = subset-full-ideal-Semiring
  pr2 full-right-ideal-Semiring = is-right-ideal-full-ideal-Semiring

  is-ideal-full-ideal-Semiring : is-ideal-subset-Semiring R
    subset-full-ideal-Semiring
  pr1 is-ideal-full-ideal-Semiring = is-additive-submonoid-full-ideal-Semiring
  pr2 is-ideal-full-ideal-Semiring {r} {x} {u} =
    is-closed-under-two-sided-multiplication-full-ideal-Semiring {r} {x} {u}

  full-ideal-Semiring : ideal-Semiring lzero R
  pr1 full-ideal-Semiring = subset-full-ideal-Semiring
  pr2 full-ideal-Semiring = is-ideal-full-ideal-Semiring

  is-full-full-ideal-Semiring : is-full-ideal-Semiring R full-ideal-Semiring
  is-full-full-ideal-Semiring x = raise-star
```

## Properties

### Any ideal is full if and only if it contains `1`

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  is-full-contains-one-ideal-Semiring :
    is-in-ideal-Semiring R I (one-Semiring R) → is-full-ideal-Semiring R I
  is-full-contains-one-ideal-Semiring H x =
    is-closed-under-eq-ideal-Semiring R I
      ( is-closed-under-left-multiplication-ideal-Semiring R I H)
      ( right-unit-law-mul-Semiring R x)

  contains-one-is-full-ideal-Semiring :
    is-full-ideal-Semiring R I → is-in-ideal-Semiring R I (one-Semiring R)
  contains-one-is-full-ideal-Semiring H = H (one-Semiring R)
```

### Any ideal is full if and only if it is a top element in the large poset of ideals

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  is-full-is-top-element-ideal-Semiring :
    is-top-element-Large-Poset (ideal-Semiring-Large-Poset R) I →
    is-full-ideal-Semiring R I
  is-full-is-top-element-ideal-Semiring H x =
    H (full-ideal-Semiring R) x (is-full-full-ideal-Semiring R x)

  is-top-element-is-full-ideal-Semiring :
    is-full-ideal-Semiring R I →
    is-top-element-Large-Poset (ideal-Semiring-Large-Poset R) I
  is-top-element-is-full-ideal-Semiring H I x K = H x

module _
  {l1 : Level} (R : Semiring l1)
  where

  is-top-element-full-ideal-Semiring :
    is-top-element-Large-Poset
      ( ideal-Semiring-Large-Poset R)
      ( full-ideal-Semiring R)
  is-top-element-full-ideal-Semiring =
    is-top-element-is-full-ideal-Semiring R
      ( full-ideal-Semiring R)
      ( is-full-full-ideal-Semiring R)

  has-top-element-ideal-Semiring :
    has-top-element-Large-Poset (ideal-Semiring-Large-Poset R)
  top-has-top-element-Large-Poset
    has-top-element-ideal-Semiring =
    full-ideal-Semiring R
  is-top-element-top-has-top-element-Large-Poset
    has-top-element-ideal-Semiring =
    is-top-element-full-ideal-Semiring
```
