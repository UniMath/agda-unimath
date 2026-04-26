# Pullbacks of ideals of semirings

```agda
module ring-theory.pullbacks-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.powersets
open import foundation.pullbacks-subtypes
open import foundation.universe-levels

open import ring-theory.homomorphisms-semirings
open import ring-theory.poset-of-ideals-semirings
open import ring-theory.semirings
open import ring-theory.ideals-semirings
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
[ideal](ring-theory.ideal-semirings.md) `K ≤ S`, the
{{concept "pullback" Disambiguation="ideal of a semiring" Agda=pullback-ideal-Semiring}}
of `K` along `f` is defined by substituting `f` in `K`. In other
words, it is the ideal `f＊K` of `R` consisting of the elements
`x : R` such that `f x ∈ K`.

## Definitions

### The pullback of a ideal along a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S) (K : ideal-Semiring l3 S)
  where

  subset-pullback-ideal-Semiring : subset-Semiring l3 R
  subset-pullback-ideal-Semiring =
    subset-ideal-Semiring S K ∘ map-hom-Semiring R S f

  contains-zero-pullback-ideal-Semiring :
    contains-zero-subset-Semiring R subset-pullback-ideal-Semiring
  contains-zero-pullback-ideal-Semiring =
    is-closed-under-eq-ideal-Semiring' S K
      ( contains-zero-ideal-Semiring S K)
      ( preserves-zero-hom-Semiring R S f)

  is-closed-under-addition-pullback-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-pullback-ideal-Semiring
  is-closed-under-addition-pullback-ideal-Semiring p q =
    is-closed-under-eq-ideal-Semiring' S K
      ( is-closed-under-addition-ideal-Semiring S K p q)
      ( preserves-addition-hom-Semiring R S f)

  is-additive-submonoid-pullback-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R subset-pullback-ideal-Semiring
  pr1 is-additive-submonoid-pullback-ideal-Semiring =
    contains-zero-pullback-ideal-Semiring
  pr2 is-additive-submonoid-pullback-ideal-Semiring =
    is-closed-under-addition-pullback-ideal-Semiring

  is-closed-under-two-sided-multiplication-pullback-ideal-Semiring :
    is-closed-under-two-sided-multiplication-subset-Semiring R
      subset-pullback-ideal-Semiring
  is-closed-under-two-sided-multiplication-pullback-ideal-Semiring {r} {x} {u} p =
    is-closed-under-eq-ideal-Semiring' S K
      ( is-closed-under-two-sided-multiplication-ideal-Semiring S K p)
      ( preserves-mul-hom-Semiring R S f ∙
        ap (mul-Semiring' S _) (preserves-mul-hom-Semiring R S f))

  is-closed-under-multiplication-pullback-ideal-Semiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-pullback-ideal-Semiring
  is-closed-under-multiplication-pullback-ideal-Semiring p q =
    is-closed-under-eq-ideal-Semiring' S K
      ( is-closed-under-multiplication-ideal-Semiring S K p q)
      ( preserves-mul-hom-Semiring R S f)

  pullback-ideal-Semiring : ideal-Semiring l3 R
  pr1 pullback-ideal-Semiring =
    subset-pullback-ideal-Semiring
  pr1 (pr2 pullback-ideal-Semiring) =
    is-additive-submonoid-pullback-ideal-Semiring
  pr2 (pr2 pullback-ideal-Semiring) =
    is-closed-under-two-sided-multiplication-pullback-ideal-Semiring

  is-in-pullback-ideal-Semiring : type-Semiring R → UU l3
  is-in-pullback-ideal-Semiring =
    is-in-ideal-Semiring R pullback-ideal-Semiring

  is-closed-under-eq-pullback-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-pullback-ideal-Semiring x → x ＝ y → is-in-pullback-ideal-Semiring y
  is-closed-under-eq-pullback-ideal-Semiring =
    is-closed-under-eq-ideal-Semiring R pullback-ideal-Semiring

  is-closed-under-eq-pullback-ideal-Semiring' :
    {x y : type-Semiring R} →
    is-in-pullback-ideal-Semiring y → x ＝ y → is-in-pullback-ideal-Semiring x
  is-closed-under-eq-pullback-ideal-Semiring' =
    is-closed-under-eq-ideal-Semiring' R pullback-ideal-Semiring
```

### The order preserving operation `pullback-ideal-Semiring`

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-pullback-ideal-Semiring :
    {l3 l4 : Level} (U : ideal-Semiring l3 S) (V : ideal-Semiring l4 S) →
    leq-ideal-Semiring S U V →
    leq-ideal-Semiring R
      ( pullback-ideal-Semiring R S f U)
      ( pullback-ideal-Semiring R S f V)
  preserves-order-pullback-ideal-Semiring U V =
    preserves-order-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-ideal-Semiring S U)
      ( subset-ideal-Semiring S V)

  pullback-hom-large-poset-ideal-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( ideal-Semiring-Large-Poset S)
      ( ideal-Semiring-Large-Poset R)
  map-hom-Large-Preorder pullback-hom-large-poset-ideal-Semiring =
    pullback-ideal-Semiring R S f
  preserves-order-hom-Large-Preorder pullback-hom-large-poset-ideal-Semiring =
    preserves-order-pullback-ideal-Semiring
```

## Properties

### The pullback operation commutes with the underlying subtype operation

The square

```text
                             pullback f
    ideal-Semiring S ----------------> ideal-Semiring R
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

  coherence-square-pullback-subset-ideal-Semiring :
    coherence-square-hom-Large-Poset
      ( ideal-Semiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring S))
      ( ideal-Semiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
      ( pullback-hom-large-poset-ideal-Semiring R S f)
      ( subset-ideal-hom-large-poset-Semiring S)
      ( subset-ideal-hom-large-poset-Semiring R)
      ( pullback-subtype-hom-Large-Poset (map-hom-Semiring R S f))
  coherence-square-pullback-subset-ideal-Semiring =
    refl-sim-hom-Large-Poset
      ( ideal-Semiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring R))
      ( comp-hom-Large-Poset
        ( ideal-Semiring-Large-Poset S)
        ( ideal-Semiring-Large-Poset R)
        ( powerset-Large-Poset (type-Semiring R))
        ( subset-ideal-hom-large-poset-Semiring R)
        ( pullback-hom-large-poset-ideal-Semiring R S f))
```
