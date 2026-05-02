# Pullbacks of subtractive left ideals in semirings

```agda
module ring-theory.pullbacks-subtractive-left-ideals-semirings where
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
open import ring-theory.left-ideals-semirings
open import ring-theory.poset-of-left-ideals-semirings
open import ring-theory.poset-of-subtractive-left-ideals-semirings
open import ring-theory.pullbacks-left-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subtractive-left-ideals-semirings
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
[subtractive left ideal](ring-theory.left-ideal-semirings.md) `K ≤ S`, the
{{concept "pullback" Disambiguation="subtractive left ideal of a semiring" Agda=pullback-left-ideal-Semiring}}
of `K` along `f` is again a subtractive left ideal. It is defined as the left ideal `f＊K` of `R` consisting of the elements
`x : R` such that `f x ∈ K`.

## Definitions

### The pullback of a subtractive left ideal along a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S) (J : subtractive-left-ideal-Semiring l3 S)
  where

  left-ideal-pullback-subtractive-left-ideal-Semiring :
    left-ideal-Semiring l3 R
  left-ideal-pullback-subtractive-left-ideal-Semiring =
    pullback-left-ideal-Semiring R S f
      ( left-ideal-subtractive-left-ideal-Semiring S J)

  is-subtractive-pullback-subtractive-left-ideal-Semiring :
    is-subtractive-left-ideal-Semiring R
      left-ideal-pullback-subtractive-left-ideal-Semiring
  is-subtractive-pullback-subtractive-left-ideal-Semiring H K =
    is-subtractive-subtractive-left-ideal-Semiring S J H
      ( is-closed-under-eq-subtractive-left-ideal-Semiring S J K
        ( preserves-addition-hom-Semiring R S f))

  pullback-subtractive-left-ideal-Semiring :
    subtractive-left-ideal-Semiring l3 R
  pr1 pullback-subtractive-left-ideal-Semiring =
    left-ideal-pullback-subtractive-left-ideal-Semiring
  pr2 pullback-subtractive-left-ideal-Semiring =
    is-subtractive-pullback-subtractive-left-ideal-Semiring

  subset-pullback-subtractive-left-ideal-Semiring :
    subset-Semiring l3 R
  subset-pullback-subtractive-left-ideal-Semiring =
    subset-left-ideal-Semiring R
      left-ideal-pullback-subtractive-left-ideal-Semiring

  contains-zero-pullback-subtractive-left-ideal-Semiring :
    contains-zero-subset-Semiring R
      subset-pullback-subtractive-left-ideal-Semiring
  contains-zero-pullback-subtractive-left-ideal-Semiring =
    contains-zero-left-ideal-Semiring R
      left-ideal-pullback-subtractive-left-ideal-Semiring

  is-closed-under-addition-pullback-subtractive-left-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R
      subset-pullback-subtractive-left-ideal-Semiring
  is-closed-under-addition-pullback-subtractive-left-ideal-Semiring =
    is-closed-under-addition-left-ideal-Semiring R
      left-ideal-pullback-subtractive-left-ideal-Semiring

  is-additive-submonoid-pullback-subtractive-left-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R
      subset-pullback-subtractive-left-ideal-Semiring
  is-additive-submonoid-pullback-subtractive-left-ideal-Semiring =
    is-additive-submonoid-left-ideal-Semiring R
      left-ideal-pullback-subtractive-left-ideal-Semiring

  is-closed-under-left-multiplication-pullback-subtractive-left-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-pullback-subtractive-left-ideal-Semiring
  is-closed-under-left-multiplication-pullback-subtractive-left-ideal-Semiring =
    is-closed-under-left-multiplication-left-ideal-Semiring R
      left-ideal-pullback-subtractive-left-ideal-Semiring

  is-closed-under-multiplication-pullback-subtractive-left-ideal-Semiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-pullback-subtractive-left-ideal-Semiring
  is-closed-under-multiplication-pullback-subtractive-left-ideal-Semiring =
    is-closed-under-multiplication-left-ideal-Semiring R
      left-ideal-pullback-subtractive-left-ideal-Semiring

  is-in-pullback-subtractive-left-ideal-Semiring : type-Semiring R → UU l3
  is-in-pullback-subtractive-left-ideal-Semiring =
    is-in-left-ideal-Semiring R
      left-ideal-pullback-subtractive-left-ideal-Semiring

  is-closed-under-eq-pullback-subtractive-left-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-pullback-subtractive-left-ideal-Semiring x → x ＝ y →
    is-in-pullback-subtractive-left-ideal-Semiring y
  is-closed-under-eq-pullback-subtractive-left-ideal-Semiring =
    is-closed-under-eq-left-ideal-Semiring R
      left-ideal-pullback-subtractive-left-ideal-Semiring

  is-closed-under-eq-pullback-subtractive-left-ideal-Semiring' :
    {x y : type-Semiring R} →
    is-in-pullback-subtractive-left-ideal-Semiring y → x ＝ y →
    is-in-pullback-subtractive-left-ideal-Semiring x
  is-closed-under-eq-pullback-subtractive-left-ideal-Semiring' =
    is-closed-under-eq-left-ideal-Semiring' R
      left-ideal-pullback-subtractive-left-ideal-Semiring
```

### Pullback of subtractive left ideals is order preserving

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-pullback-subtractive-left-ideal-Semiring :
    {l3 l4 : Level}
    (U : subtractive-left-ideal-Semiring l3 S)
    (V : subtractive-left-ideal-Semiring l4 S) →
    leq-subtractive-left-ideal-Semiring S U V →
    leq-subtractive-left-ideal-Semiring R
      ( pullback-subtractive-left-ideal-Semiring R S f U)
      ( pullback-subtractive-left-ideal-Semiring R S f V)
  preserves-order-pullback-subtractive-left-ideal-Semiring U V =
    preserves-order-pullback-left-ideal-Semiring R S f
      ( left-ideal-subtractive-left-ideal-Semiring S U)
      ( left-ideal-subtractive-left-ideal-Semiring S V)

  pullback-hom-large-poset-subtractive-left-ideal-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( subtractive-left-ideal-Semiring-Large-Poset S)
      ( subtractive-left-ideal-Semiring-Large-Poset R)
  map-hom-Large-Preorder
    pullback-hom-large-poset-subtractive-left-ideal-Semiring =
    pullback-subtractive-left-ideal-Semiring R S f
  preserves-order-hom-Large-Preorder
    pullback-hom-large-poset-subtractive-left-ideal-Semiring =
    preserves-order-pullback-subtractive-left-ideal-Semiring
```

## Properties

### The pullback operation commutes with the underlying left ideal operation

The square

```text
                                    pullback f
  subtractive-left-ideal-Semiring S ---------> subtractive-left-ideal-Semiring R
              |                                       |
       K ↦ UK |                                       | K ↦ UK
              |                                       |
              ∨                                       ∨
       left-ideal-Semiring S -------------> left-ideal-Semiring R
                               pullback f
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.md)
by reflexivity.

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  coherence-square-pullback-left-ideal-subtractive-left-ideal-Semiring :
    coherence-square-hom-Large-Poset
      ( subtractive-left-ideal-Semiring-Large-Poset S)
      ( left-ideal-Semiring-Large-Poset S)
      ( subtractive-left-ideal-Semiring-Large-Poset R)
      ( left-ideal-Semiring-Large-Poset R)
      ( pullback-hom-large-poset-subtractive-left-ideal-Semiring R S f)
      ( left-ideal-subtractive-left-ideal-hom-large-poset-Semiring S)
      ( left-ideal-subtractive-left-ideal-hom-large-poset-Semiring R)
      ( pullback-hom-large-poset-left-ideal-Semiring R S f)
  coherence-square-pullback-left-ideal-subtractive-left-ideal-Semiring =
    refl-sim-hom-Large-Poset
      ( subtractive-left-ideal-Semiring-Large-Poset S)
      ( left-ideal-Semiring-Large-Poset R)
      ( comp-hom-Large-Poset
        ( subtractive-left-ideal-Semiring-Large-Poset S)
        ( subtractive-left-ideal-Semiring-Large-Poset R)
        ( left-ideal-Semiring-Large-Poset R)
        ( left-ideal-subtractive-left-ideal-hom-large-poset-Semiring R)
        ( pullback-hom-large-poset-subtractive-left-ideal-Semiring R S f))
```
