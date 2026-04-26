# Pullbacks of left ideals of semirings

```agda
module ring-theory.pullbacks-left-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.powersets
open import foundation.pullbacks-subtypes
open import foundation.universe-levels

open import ring-theory.homomorphisms-semirings
open import ring-theory.poset-of-left-ideals-semirings
open import ring-theory.semirings
open import ring-theory.left-ideals-semirings
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
[left ideal](ring-theory.left-ideal-semirings.md) `K ≤ S`, the
{{concept "pullback" Disambiguation="left ideal of a semiring" Agda=pullback-left-ideal-Semiring}}
of `K` along `f` is defined by substituting `f` in `K`. In other
words, it is the left ideal `f＊K` of `R` consisting of the elements
`x : R` such that `f x ∈ K`.

## Definitions

### The pullback of a left ideal along a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S) (K : left-ideal-Semiring l3 S)
  where

  subset-pullback-left-ideal-Semiring : subset-Semiring l3 R
  subset-pullback-left-ideal-Semiring =
    subset-left-ideal-Semiring S K ∘ map-hom-Semiring R S f

  contains-zero-pullback-left-ideal-Semiring :
    contains-zero-subset-Semiring R subset-pullback-left-ideal-Semiring
  contains-zero-pullback-left-ideal-Semiring =
    is-closed-under-eq-left-ideal-Semiring' S K
      ( contains-zero-left-ideal-Semiring S K)
      ( preserves-zero-hom-Semiring R S f)

  is-closed-under-addition-pullback-left-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-pullback-left-ideal-Semiring
  is-closed-under-addition-pullback-left-ideal-Semiring p q =
    is-closed-under-eq-left-ideal-Semiring' S K
      ( is-closed-under-addition-left-ideal-Semiring S K p q)
      ( preserves-addition-hom-Semiring R S f)

  is-additive-submonoid-pullback-left-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R subset-pullback-left-ideal-Semiring
  pr1 is-additive-submonoid-pullback-left-ideal-Semiring =
    contains-zero-pullback-left-ideal-Semiring
  pr2 is-additive-submonoid-pullback-left-ideal-Semiring =
    is-closed-under-addition-pullback-left-ideal-Semiring

  is-closed-under-left-multiplication-pullback-left-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-pullback-left-ideal-Semiring
  is-closed-under-left-multiplication-pullback-left-ideal-Semiring p =
    is-closed-under-eq-left-ideal-Semiring' S K
      ( is-closed-under-left-multiplication-left-ideal-Semiring S K p)
      ( preserves-mul-hom-Semiring R S f)

  is-closed-under-multiplication-pullback-left-ideal-Semiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-pullback-left-ideal-Semiring
  is-closed-under-multiplication-pullback-left-ideal-Semiring p q =
    is-closed-under-eq-left-ideal-Semiring' S K
      ( is-closed-under-multiplication-left-ideal-Semiring S K p q)
      ( preserves-mul-hom-Semiring R S f)

  pullback-left-ideal-Semiring : left-ideal-Semiring l3 R
  pr1 pullback-left-ideal-Semiring =
    subset-pullback-left-ideal-Semiring
  pr1 (pr2 pullback-left-ideal-Semiring) =
    is-additive-submonoid-pullback-left-ideal-Semiring
  pr2 (pr2 pullback-left-ideal-Semiring) =
    is-closed-under-left-multiplication-pullback-left-ideal-Semiring

  is-in-pullback-left-ideal-Semiring : type-Semiring R → UU l3
  is-in-pullback-left-ideal-Semiring =
    is-in-left-ideal-Semiring R pullback-left-ideal-Semiring

  is-closed-under-eq-pullback-left-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-pullback-left-ideal-Semiring x → x ＝ y → is-in-pullback-left-ideal-Semiring y
  is-closed-under-eq-pullback-left-ideal-Semiring =
    is-closed-under-eq-left-ideal-Semiring R pullback-left-ideal-Semiring

  is-closed-under-eq-pullback-left-ideal-Semiring' :
    {x y : type-Semiring R} →
    is-in-pullback-left-ideal-Semiring y → x ＝ y → is-in-pullback-left-ideal-Semiring x
  is-closed-under-eq-pullback-left-ideal-Semiring' =
    is-closed-under-eq-left-ideal-Semiring' R pullback-left-ideal-Semiring
```

### The order preserving operation `pullback-left-ideal-Semiring`

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-pullback-left-ideal-Semiring :
    {l3 l4 : Level} (U : left-ideal-Semiring l3 S) (V : left-ideal-Semiring l4 S) →
    leq-left-ideal-Semiring S U V →
    leq-left-ideal-Semiring R
      ( pullback-left-ideal-Semiring R S f U)
      ( pullback-left-ideal-Semiring R S f V)
  preserves-order-pullback-left-ideal-Semiring U V =
    preserves-order-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-left-ideal-Semiring S U)
      ( subset-left-ideal-Semiring S V)

  pullback-hom-large-poset-left-ideal-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( left-ideal-Semiring-Large-Poset S)
      ( left-ideal-Semiring-Large-Poset R)
  map-hom-Large-Preorder pullback-hom-large-poset-left-ideal-Semiring =
    pullback-left-ideal-Semiring R S f
  preserves-order-hom-Large-Preorder pullback-hom-large-poset-left-ideal-Semiring =
    preserves-order-pullback-left-ideal-Semiring
```

## Properties

### The pullback operation commutes with the underlying subtype operation

The square

```text
                             pullback f
    left-ideal-Semiring S ----------------> left-ideal-Semiring R
              |                                       |
       K ↦ UK |                                       | K ↦ UK
              |                                       |
              ∨                                       ∨
        subset-Semiring S --------------------> subset-Semiring R
                                pullback f
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.md)
by reflexivity.

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  coherence-square-pullback-subset-left-ideal-Semiring :
    coherence-square-hom-Large-Poset
      ( left-ideal-Semiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring S))
      ( left-ideal-Semiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
      ( pullback-hom-large-poset-left-ideal-Semiring R S f)
      ( subset-left-ideal-hom-large-poset-Semiring S)
      ( subset-left-ideal-hom-large-poset-Semiring R)
      ( pullback-subtype-hom-Large-Poset (map-hom-Semiring R S f))
  coherence-square-pullback-subset-left-ideal-Semiring =
    refl-sim-hom-Large-Poset
      ( left-ideal-Semiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring R))
      ( comp-hom-Large-Poset
        ( left-ideal-Semiring-Large-Poset S)
        ( left-ideal-Semiring-Large-Poset R)
        ( powerset-Large-Poset (type-Semiring R))
        ( subset-left-ideal-hom-large-poset-Semiring R)
        ( pullback-hom-large-poset-left-ideal-Semiring R S f))
```
