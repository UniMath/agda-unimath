# Pullbacks of subtractive right ideals in semirings

```agda
module ring-theory.pullbacks-subtractive-right-ideals-semirings where
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
open import ring-theory.right-ideals-semirings
open import ring-theory.poset-of-right-ideals-semirings
open import ring-theory.poset-of-subtractive-right-ideals-semirings
open import ring-theory.pullbacks-right-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subtractive-right-ideals-semirings
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
[subtractive right ideal](ring-theory.right-ideal-semirings.md) `K ≤ S`, the
{{concept "pullback" Disambiguation="subtractive right ideal of a semiring" Agda=pullback-right-ideal-Semiring}}
of `K` along `f` is again a subtractive right ideal. It is defined as the right ideal `f＊K` of `R` consisting of the elements
`x : R` such that `f x ∈ K`.

## Definitions

### The pullback of a subtractive right ideal along a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S) (J : subtractive-right-ideal-Semiring l3 S)
  where

  right-ideal-pullback-subtractive-right-ideal-Semiring :
    right-ideal-Semiring l3 R
  right-ideal-pullback-subtractive-right-ideal-Semiring =
    pullback-right-ideal-Semiring R S f
      ( right-ideal-subtractive-right-ideal-Semiring S J)

  is-subtractive-pullback-subtractive-right-ideal-Semiring :
    is-subtractive-right-ideal-Semiring R
      right-ideal-pullback-subtractive-right-ideal-Semiring
  is-subtractive-pullback-subtractive-right-ideal-Semiring H K =
    is-subtractive-subtractive-right-ideal-Semiring S J H
      ( is-closed-under-eq-subtractive-right-ideal-Semiring S J K
        ( preserves-addition-hom-Semiring R S f))

  pullback-subtractive-right-ideal-Semiring :
    subtractive-right-ideal-Semiring l3 R
  pr1 pullback-subtractive-right-ideal-Semiring =
    right-ideal-pullback-subtractive-right-ideal-Semiring
  pr2 pullback-subtractive-right-ideal-Semiring =
    is-subtractive-pullback-subtractive-right-ideal-Semiring

  subset-pullback-subtractive-right-ideal-Semiring :
    subset-Semiring l3 R
  subset-pullback-subtractive-right-ideal-Semiring =
    subset-right-ideal-Semiring R
      right-ideal-pullback-subtractive-right-ideal-Semiring

  contains-zero-pullback-subtractive-right-ideal-Semiring :
    contains-zero-subset-Semiring R
      subset-pullback-subtractive-right-ideal-Semiring
  contains-zero-pullback-subtractive-right-ideal-Semiring =
    contains-zero-right-ideal-Semiring R
      right-ideal-pullback-subtractive-right-ideal-Semiring

  is-closed-under-addition-pullback-subtractive-right-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R
      subset-pullback-subtractive-right-ideal-Semiring
  is-closed-under-addition-pullback-subtractive-right-ideal-Semiring =
    is-closed-under-addition-right-ideal-Semiring R
      right-ideal-pullback-subtractive-right-ideal-Semiring

  is-additive-submonoid-pullback-subtractive-right-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R
      subset-pullback-subtractive-right-ideal-Semiring
  is-additive-submonoid-pullback-subtractive-right-ideal-Semiring =
    is-additive-submonoid-right-ideal-Semiring R
      right-ideal-pullback-subtractive-right-ideal-Semiring

  is-closed-under-right-multiplication-pullback-subtractive-right-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-pullback-subtractive-right-ideal-Semiring
  is-closed-under-right-multiplication-pullback-subtractive-right-ideal-Semiring =
    is-closed-under-right-multiplication-right-ideal-Semiring R
      right-ideal-pullback-subtractive-right-ideal-Semiring

  is-closed-under-multiplication-pullback-subtractive-right-ideal-Semiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-pullback-subtractive-right-ideal-Semiring
  is-closed-under-multiplication-pullback-subtractive-right-ideal-Semiring =
    is-closed-under-multiplication-right-ideal-Semiring R
      right-ideal-pullback-subtractive-right-ideal-Semiring

  is-in-pullback-subtractive-right-ideal-Semiring : type-Semiring R → UU l3
  is-in-pullback-subtractive-right-ideal-Semiring =
    is-in-right-ideal-Semiring R
      right-ideal-pullback-subtractive-right-ideal-Semiring

  is-closed-under-eq-pullback-subtractive-right-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-pullback-subtractive-right-ideal-Semiring x → x ＝ y →
    is-in-pullback-subtractive-right-ideal-Semiring y
  is-closed-under-eq-pullback-subtractive-right-ideal-Semiring =
    is-closed-under-eq-right-ideal-Semiring R
      right-ideal-pullback-subtractive-right-ideal-Semiring

  is-closed-under-eq-pullback-subtractive-right-ideal-Semiring' :
    {x y : type-Semiring R} →
    is-in-pullback-subtractive-right-ideal-Semiring y → x ＝ y →
    is-in-pullback-subtractive-right-ideal-Semiring x
  is-closed-under-eq-pullback-subtractive-right-ideal-Semiring' =
    is-closed-under-eq-right-ideal-Semiring' R
      right-ideal-pullback-subtractive-right-ideal-Semiring
```

### Pullback of subtractive right ideals is order preserving

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-pullback-subtractive-right-ideal-Semiring :
    {l3 l4 : Level}
    (U : subtractive-right-ideal-Semiring l3 S)
    (V : subtractive-right-ideal-Semiring l4 S) →
    leq-subtractive-right-ideal-Semiring S U V →
    leq-subtractive-right-ideal-Semiring R
      ( pullback-subtractive-right-ideal-Semiring R S f U)
      ( pullback-subtractive-right-ideal-Semiring R S f V)
  preserves-order-pullback-subtractive-right-ideal-Semiring U V =
    preserves-order-pullback-right-ideal-Semiring R S f
      ( right-ideal-subtractive-right-ideal-Semiring S U)
      ( right-ideal-subtractive-right-ideal-Semiring S V)

  pullback-hom-large-poset-subtractive-right-ideal-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( subtractive-right-ideal-Semiring-Large-Poset S)
      ( subtractive-right-ideal-Semiring-Large-Poset R)
  map-hom-Large-Preorder
    pullback-hom-large-poset-subtractive-right-ideal-Semiring =
    pullback-subtractive-right-ideal-Semiring R S f
  preserves-order-hom-Large-Preorder
    pullback-hom-large-poset-subtractive-right-ideal-Semiring =
    preserves-order-pullback-subtractive-right-ideal-Semiring
```

## Properties

### The pullback operation commutes with the underlying right ideal operation

The square

```text
                                   pullback f
subtractive-right-ideal-Semiring S ---------> subtractive-right-ideal-Semiring R
              |                                       |
       K ↦ UK |                                       | K ↦ UK
              |                                       |
              ∨                                       ∨
       right-ideal-Semiring S -------------> right-ideal-Semiring R
                               pullback f
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.md)
by reflexivity.

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  coherence-square-pullback-right-ideal-subtractive-right-ideal-Semiring :
    coherence-square-hom-Large-Poset
      ( subtractive-right-ideal-Semiring-Large-Poset S)
      ( right-ideal-Semiring-Large-Poset S)
      ( subtractive-right-ideal-Semiring-Large-Poset R)
      ( right-ideal-Semiring-Large-Poset R)
      ( pullback-hom-large-poset-subtractive-right-ideal-Semiring R S f)
      ( right-ideal-subtractive-right-ideal-hom-large-poset-Semiring S)
      ( right-ideal-subtractive-right-ideal-hom-large-poset-Semiring R)
      ( pullback-hom-large-poset-right-ideal-Semiring R S f)
  coherence-square-pullback-right-ideal-subtractive-right-ideal-Semiring =
    refl-sim-hom-Large-Poset
      ( subtractive-right-ideal-Semiring-Large-Poset S)
      ( right-ideal-Semiring-Large-Poset R)
      ( comp-hom-Large-Poset
        ( subtractive-right-ideal-Semiring-Large-Poset S)
        ( subtractive-right-ideal-Semiring-Large-Poset R)
        ( right-ideal-Semiring-Large-Poset R)
        ( right-ideal-subtractive-right-ideal-hom-large-poset-Semiring R)
        ( pullback-hom-large-poset-subtractive-right-ideal-Semiring R S f))
```
