# Pullbacks of subtractive ideals in semirings

```agda
module ring-theory.pullbacks-subtractive-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.pullbacks-subtypes
open import foundation.universe-levels

open import ring-theory.homomorphisms-semirings
open import ring-theory.ideals-semirings
open import ring-theory.poset-of-ideals-semirings
open import ring-theory.poset-of-subtractive-ideals-semirings
open import ring-theory.pullbacks-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subtractive-ideals-semirings
open import ring-theory.subsets-semirings

open import order-theory.commuting-squares-of-order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-order-preserving-maps-large-posets
```

</details>

## Idea

Given a [semiring homomorphism](ring-theory.homomorphisms-semirings.md)
`f : R → S` into a [semiring](ring-theory.semirings.md) `S` equipped with a
[subtractive ideal](ring-theory.ideal-semirings.md) `K ≤ S`, the
{{concept "pullback" Disambiguation="subtractive ideal of a semiring" Agda=pullback-ideal-Semiring}}
of `K` along `f` is again a subtractive ideal. It is defined as the ideal `f＊K` of `R` consisting of the elements
`x : R` such that `f x ∈ K`.

## Definitions

### The pullback of a subtractive ideal along a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S) (J : subtractive-ideal-Semiring l3 S)
  where

  ideal-pullback-subtractive-ideal-Semiring :
    ideal-Semiring l3 R
  ideal-pullback-subtractive-ideal-Semiring =
    pullback-ideal-Semiring R S f (ideal-subtractive-ideal-Semiring S J)

  is-subtractive-pullback-subtractive-ideal-Semiring :
    is-subtractive-ideal-Semiring R ideal-pullback-subtractive-ideal-Semiring
  is-subtractive-pullback-subtractive-ideal-Semiring H K =
    is-subtractive-subtractive-ideal-Semiring S J H
      ( is-closed-under-eq-subtractive-ideal-Semiring S J K
        ( preserves-addition-hom-Semiring R S f))

  pullback-subtractive-ideal-Semiring :
    subtractive-ideal-Semiring l3 R
  pr1 pullback-subtractive-ideal-Semiring =
    ideal-pullback-subtractive-ideal-Semiring
  pr2 pullback-subtractive-ideal-Semiring =
    is-subtractive-pullback-subtractive-ideal-Semiring

  subset-pullback-subtractive-ideal-Semiring :
    subset-Semiring l3 R
  subset-pullback-subtractive-ideal-Semiring =
    subset-ideal-Semiring R ideal-pullback-subtractive-ideal-Semiring

  contains-zero-pullback-subtractive-ideal-Semiring :
    contains-zero-subset-Semiring R subset-pullback-subtractive-ideal-Semiring
  contains-zero-pullback-subtractive-ideal-Semiring =
    contains-zero-ideal-Semiring R ideal-pullback-subtractive-ideal-Semiring

  is-closed-under-addition-pullback-subtractive-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R
      subset-pullback-subtractive-ideal-Semiring
  is-closed-under-addition-pullback-subtractive-ideal-Semiring =
    is-closed-under-addition-ideal-Semiring R
      ideal-pullback-subtractive-ideal-Semiring

  is-additive-submonoid-pullback-subtractive-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R
      subset-pullback-subtractive-ideal-Semiring
  is-additive-submonoid-pullback-subtractive-ideal-Semiring =
    is-additive-submonoid-ideal-Semiring R
      ideal-pullback-subtractive-ideal-Semiring

  is-closed-under-two-sided-multiplication-pullback-subtractive-ideal-Semiring :
    is-closed-under-two-sided-multiplication-subset-Semiring R
      subset-pullback-subtractive-ideal-Semiring
  is-closed-under-two-sided-multiplication-pullback-subtractive-ideal-Semiring =
    is-closed-under-two-sided-multiplication-ideal-Semiring R
      ideal-pullback-subtractive-ideal-Semiring

  is-closed-under-multiplication-pullback-subtractive-ideal-Semiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-pullback-subtractive-ideal-Semiring
  is-closed-under-multiplication-pullback-subtractive-ideal-Semiring =
    is-closed-under-multiplication-ideal-Semiring R
      ideal-pullback-subtractive-ideal-Semiring

  is-in-pullback-subtractive-ideal-Semiring : type-Semiring R → UU l3
  is-in-pullback-subtractive-ideal-Semiring =
    is-in-ideal-Semiring R ideal-pullback-subtractive-ideal-Semiring

  is-closed-under-eq-pullback-subtractive-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-pullback-subtractive-ideal-Semiring x → x ＝ y →
    is-in-pullback-subtractive-ideal-Semiring y
  is-closed-under-eq-pullback-subtractive-ideal-Semiring =
    is-closed-under-eq-ideal-Semiring R
      ideal-pullback-subtractive-ideal-Semiring

  is-closed-under-eq-pullback-subtractive-ideal-Semiring' :
    {x y : type-Semiring R} →
    is-in-pullback-subtractive-ideal-Semiring y → x ＝ y →
    is-in-pullback-subtractive-ideal-Semiring x
  is-closed-under-eq-pullback-subtractive-ideal-Semiring' =
    is-closed-under-eq-ideal-Semiring' R
      ideal-pullback-subtractive-ideal-Semiring
```

### Pullback of subtractive ideals is order preserving

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-pullback-subtractive-ideal-Semiring :
    {l3 l4 : Level}
    (U : subtractive-ideal-Semiring l3 S)
    (V : subtractive-ideal-Semiring l4 S) →
    leq-subtractive-ideal-Semiring S U V →
    leq-subtractive-ideal-Semiring R
      ( pullback-subtractive-ideal-Semiring R S f U)
      ( pullback-subtractive-ideal-Semiring R S f V)
  preserves-order-pullback-subtractive-ideal-Semiring U V =
    preserves-order-pullback-ideal-Semiring R S f
      ( ideal-subtractive-ideal-Semiring S U)
      ( ideal-subtractive-ideal-Semiring S V)

  pullback-hom-large-poset-subtractive-ideal-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( subtractive-ideal-Semiring-Large-Poset S)
      ( subtractive-ideal-Semiring-Large-Poset R)
  map-hom-Large-Preorder
    pullback-hom-large-poset-subtractive-ideal-Semiring =
    pullback-subtractive-ideal-Semiring R S f
  preserves-order-hom-Large-Preorder
    pullback-hom-large-poset-subtractive-ideal-Semiring =
    preserves-order-pullback-subtractive-ideal-Semiring
```

## Properties

### The pullback operation commutes with the underlying ideal operation

The square

```text
                                   pullback f
  subtractive-ideal-Semiring S ----------------> subtractive-ideal-Semiring R
              |                                       |
       K ↦ UK |                                       | K ↦ UK
              |                                       |
              ∨                                       ∨
       ideal-Semiring S --------------------> ideal-Semiring R
                             pullback f
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.md)
by reflexivity.

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  coherence-square-pullback-ideal-subtractive-ideal-Semiring :
    coherence-square-hom-Large-Poset
      ( subtractive-ideal-Semiring-Large-Poset S)
      ( ideal-Semiring-Large-Poset S)
      ( subtractive-ideal-Semiring-Large-Poset R)
      ( ideal-Semiring-Large-Poset R)
      ( pullback-hom-large-poset-subtractive-ideal-Semiring R S f)
      ( ideal-subtractive-ideal-hom-large-poset-Semiring S)
      ( ideal-subtractive-ideal-hom-large-poset-Semiring R)
      ( pullback-hom-large-poset-ideal-Semiring R S f)
  coherence-square-pullback-ideal-subtractive-ideal-Semiring =
    refl-sim-hom-Large-Poset
      ( subtractive-ideal-Semiring-Large-Poset S)
      ( ideal-Semiring-Large-Poset R)
      ( comp-hom-Large-Poset
        ( subtractive-ideal-Semiring-Large-Poset S)
        ( subtractive-ideal-Semiring-Large-Poset R)
        ( ideal-Semiring-Large-Poset R)
        ( ideal-subtractive-ideal-hom-large-poset-Semiring R)
        ( pullback-hom-large-poset-subtractive-ideal-Semiring R S f))
```
