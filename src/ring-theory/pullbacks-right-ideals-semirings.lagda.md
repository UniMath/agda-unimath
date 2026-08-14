# Pullbacks of right ideals of semirings

```agda
module ring-theory.pullbacks-right-ideals-semirings where
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
open import ring-theory.poset-of-right-ideals-semirings
open import ring-theory.semirings
open import ring-theory.right-ideals-semirings
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
[right ideal](ring-theory.right-ideal-semirings.md) `K ≤ S`, the
{{concept "pullback" Disambiguation="right ideal of a semiring" Agda=pullback-right-ideal-Semiring}}
of `K` along `f` is defined by substituting `f` in `K`. In other
words, it is the right ideal `f＊K` of `R` consisting of the elements
`x : R` such that `f x ∈ K`.

## Definitions

### The pullback of a right ideal along a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S) (K : right-ideal-Semiring l3 S)
  where

  subset-pullback-right-ideal-Semiring : subset-Semiring l3 R
  subset-pullback-right-ideal-Semiring =
    subset-right-ideal-Semiring S K ∘ map-hom-Semiring R S f

  contains-zero-pullback-right-ideal-Semiring :
    contains-zero-subset-Semiring R subset-pullback-right-ideal-Semiring
  contains-zero-pullback-right-ideal-Semiring =
    is-closed-under-eq-right-ideal-Semiring' S K
      ( contains-zero-right-ideal-Semiring S K)
      ( preserves-zero-hom-Semiring R S f)

  is-closed-under-addition-pullback-right-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-pullback-right-ideal-Semiring
  is-closed-under-addition-pullback-right-ideal-Semiring p q =
    is-closed-under-eq-right-ideal-Semiring' S K
      ( is-closed-under-addition-right-ideal-Semiring S K p q)
      ( preserves-addition-hom-Semiring R S f)

  is-additive-submonoid-pullback-right-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R subset-pullback-right-ideal-Semiring
  pr1 is-additive-submonoid-pullback-right-ideal-Semiring =
    contains-zero-pullback-right-ideal-Semiring
  pr2 is-additive-submonoid-pullback-right-ideal-Semiring =
    is-closed-under-addition-pullback-right-ideal-Semiring

  is-closed-under-right-multiplication-pullback-right-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-pullback-right-ideal-Semiring
  is-closed-under-right-multiplication-pullback-right-ideal-Semiring p =
    is-closed-under-eq-right-ideal-Semiring' S K
      ( is-closed-under-right-multiplication-right-ideal-Semiring S K p)
      ( preserves-mul-hom-Semiring R S f)

  is-closed-under-multiplication-pullback-right-ideal-Semiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-pullback-right-ideal-Semiring
  is-closed-under-multiplication-pullback-right-ideal-Semiring p q =
    is-closed-under-eq-right-ideal-Semiring' S K
      ( is-closed-under-multiplication-right-ideal-Semiring S K p q)
      ( preserves-mul-hom-Semiring R S f)

  pullback-right-ideal-Semiring : right-ideal-Semiring l3 R
  pr1 pullback-right-ideal-Semiring =
    subset-pullback-right-ideal-Semiring
  pr1 (pr2 pullback-right-ideal-Semiring) =
    is-additive-submonoid-pullback-right-ideal-Semiring
  pr2 (pr2 pullback-right-ideal-Semiring) =
    is-closed-under-right-multiplication-pullback-right-ideal-Semiring

  is-in-pullback-right-ideal-Semiring : type-Semiring R → UU l3
  is-in-pullback-right-ideal-Semiring =
    is-in-right-ideal-Semiring R pullback-right-ideal-Semiring

  is-closed-under-eq-pullback-right-ideal-Semiring :
    {x y : type-Semiring R} →
    is-in-pullback-right-ideal-Semiring x → x ＝ y → is-in-pullback-right-ideal-Semiring y
  is-closed-under-eq-pullback-right-ideal-Semiring =
    is-closed-under-eq-right-ideal-Semiring R pullback-right-ideal-Semiring

  is-closed-under-eq-pullback-right-ideal-Semiring' :
    {x y : type-Semiring R} →
    is-in-pullback-right-ideal-Semiring y → x ＝ y → is-in-pullback-right-ideal-Semiring x
  is-closed-under-eq-pullback-right-ideal-Semiring' =
    is-closed-under-eq-right-ideal-Semiring' R pullback-right-ideal-Semiring
```

### The order preserving operation `pullback-right-ideal-Semiring`

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-pullback-right-ideal-Semiring :
    {l3 l4 : Level} (U : right-ideal-Semiring l3 S) (V : right-ideal-Semiring l4 S) →
    leq-right-ideal-Semiring S U V →
    leq-right-ideal-Semiring R
      ( pullback-right-ideal-Semiring R S f U)
      ( pullback-right-ideal-Semiring R S f V)
  preserves-order-pullback-right-ideal-Semiring U V =
    preserves-order-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-right-ideal-Semiring S U)
      ( subset-right-ideal-Semiring S V)

  pullback-hom-large-poset-right-ideal-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( right-ideal-Semiring-Large-Poset S)
      ( right-ideal-Semiring-Large-Poset R)
  map-hom-Large-Preorder pullback-hom-large-poset-right-ideal-Semiring =
    pullback-right-ideal-Semiring R S f
  preserves-order-hom-Large-Preorder pullback-hom-large-poset-right-ideal-Semiring =
    preserves-order-pullback-right-ideal-Semiring
```

## Properties

### The pullback operation commutes with the underlying subtype operation

The square

```text
                             pullback f
    right-ideal-Semiring S ----------------> right-ideal-Semiring R
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

  coherence-square-pullback-subset-right-ideal-Semiring :
    coherence-square-hom-Large-Poset
      ( right-ideal-Semiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring S))
      ( right-ideal-Semiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
      ( pullback-hom-large-poset-right-ideal-Semiring R S f)
      ( subset-right-ideal-hom-large-poset-Semiring S)
      ( subset-right-ideal-hom-large-poset-Semiring R)
      ( pullback-subtype-hom-Large-Poset (map-hom-Semiring R S f))
  coherence-square-pullback-subset-right-ideal-Semiring =
    refl-sim-hom-Large-Poset
      ( right-ideal-Semiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring R))
      ( comp-hom-Large-Poset
        ( right-ideal-Semiring-Large-Poset S)
        ( right-ideal-Semiring-Large-Poset R)
        ( powerset-Large-Poset (type-Semiring R))
        ( subset-right-ideal-hom-large-poset-Semiring R)
        ( pullback-hom-large-poset-right-ideal-Semiring R S f))
```
