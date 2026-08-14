# Pullbacks of subsemirings

```agda
module ring-theory.pullbacks-subsemirings where
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
open import ring-theory.poset-of-subsemirings
open import ring-theory.semirings
open import ring-theory.subsemirings
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
[subsemiring](ring-theory.subsemirings.md) `K ≤ S`, the
{{concept "pullback" Disambiguation="subsemiring" Agda=pullback-Subsemiring}}
of `K` along `f` is defined by substituting `f` in `K`. In other
words, it is the subsemiring `f＊K` of `R` consisting of the elements
`x : R` such that `f x ∈ K`.

## Definitions

### The pullback of a subsemiring along a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S) (K : Subsemiring l3 S)
  where

  subset-pullback-Subsemiring : subset-Semiring l3 R
  subset-pullback-Subsemiring =
    subset-Subsemiring S K ∘ map-hom-Semiring R S f

  contains-zero-pullback-Subsemiring :
    contains-zero-subset-Semiring R subset-pullback-Subsemiring
  contains-zero-pullback-Subsemiring =
    is-closed-under-eq-Subsemiring' S K
      ( contains-zero-Subsemiring S K)
      ( preserves-zero-hom-Semiring R S f)

  is-closed-under-addition-pullback-Subsemiring :
    is-closed-under-addition-subset-Semiring R subset-pullback-Subsemiring
  is-closed-under-addition-pullback-Subsemiring p q =
    is-closed-under-eq-Subsemiring' S K
      ( is-closed-under-addition-Subsemiring S K p q)
      ( preserves-addition-hom-Semiring R S f)

  is-additive-submonoid-pullback-Subsemiring :
    is-additive-submonoid-subset-Semiring R subset-pullback-Subsemiring
  pr1 is-additive-submonoid-pullback-Subsemiring =
    contains-zero-pullback-Subsemiring
  pr2 is-additive-submonoid-pullback-Subsemiring =
    is-closed-under-addition-pullback-Subsemiring

  contains-one-pullback-Subsemiring :
    contains-one-subset-Semiring R subset-pullback-Subsemiring
  contains-one-pullback-Subsemiring =
    is-closed-under-eq-Subsemiring' S K
      ( contains-one-Subsemiring S K)
      ( preserves-one-hom-Semiring R S f)

  is-closed-under-multiplication-pullback-Subsemiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-pullback-Subsemiring
  is-closed-under-multiplication-pullback-Subsemiring p q =
    is-closed-under-eq-Subsemiring' S K
      ( is-closed-under-multiplication-Subsemiring S K p q)
      ( preserves-mul-hom-Semiring R S f)

  pullback-Subsemiring : Subsemiring l3 R
  pr1 pullback-Subsemiring =
    subset-pullback-Subsemiring
  pr1 (pr2 pullback-Subsemiring) =
    is-additive-submonoid-pullback-Subsemiring
  pr1 (pr2 (pr2 pullback-Subsemiring)) =
    contains-one-pullback-Subsemiring
  pr2 (pr2 (pr2 pullback-Subsemiring)) =
    is-closed-under-multiplication-pullback-Subsemiring

  is-in-pullback-Subsemiring : type-Semiring R → UU l3
  is-in-pullback-Subsemiring =
    is-in-Subsemiring R pullback-Subsemiring

  is-closed-under-eq-pullback-Subsemiring :
    {x y : type-Semiring R} →
    is-in-pullback-Subsemiring x → x ＝ y → is-in-pullback-Subsemiring y
  is-closed-under-eq-pullback-Subsemiring =
    is-closed-under-eq-Subsemiring R pullback-Subsemiring

  is-closed-under-eq-pullback-Subsemiring' :
    {x y : type-Semiring R} →
    is-in-pullback-Subsemiring y → x ＝ y → is-in-pullback-Subsemiring x
  is-closed-under-eq-pullback-Subsemiring' =
    is-closed-under-eq-Subsemiring' R pullback-Subsemiring
```

### The order preserving operation `pullback-Subsemiring`

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-pullback-Subsemiring :
    {l3 l4 : Level} (U : Subsemiring l3 S) (V : Subsemiring l4 S) →
    leq-Subsemiring S U V →
    leq-Subsemiring R
      ( pullback-Subsemiring R S f U)
      ( pullback-Subsemiring R S f V)
  preserves-order-pullback-Subsemiring U V =
    preserves-order-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-Subsemiring S U)
      ( subset-Subsemiring S V)

  pullback-hom-large-poset-Subsemiring :
    hom-Large-Poset
      ( λ l → l)
      ( Subsemiring-Large-Poset S)
      ( Subsemiring-Large-Poset R)
  map-hom-Large-Preorder pullback-hom-large-poset-Subsemiring =
    pullback-Subsemiring R S f
  preserves-order-hom-Large-Preorder pullback-hom-large-poset-Subsemiring =
    preserves-order-pullback-Subsemiring
```

## Properties

### The pullback operation commutes with the underlying subtype operation

The square

```text
                       pullback f
    Subsemiring S ----------------> Subsemiring R
          |                                |
   K ↦ UK |                                | K ↦ UK
          |                                |
          ∨                                ∨
  subset-Semiring S ------------> subset-Semiring R
                      pullback f
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.md)
by reflexivity.

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  coherence-square-pullback-subset-Subsemiring :
    coherence-square-hom-Large-Poset
      ( Subsemiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring S))
      ( Subsemiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
      ( pullback-hom-large-poset-Subsemiring R S f)
      ( subset-subsemiring-hom-large-poset-Subsemiring S)
      ( subset-subsemiring-hom-large-poset-Subsemiring R)
      ( pullback-subtype-hom-Large-Poset (map-hom-Semiring R S f))
  coherence-square-pullback-subset-Subsemiring =
    refl-sim-hom-Large-Poset
      ( Subsemiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring R))
      ( comp-hom-Large-Poset
        ( Subsemiring-Large-Poset S)
        ( Subsemiring-Large-Poset R)
        ( powerset-Large-Poset (type-Semiring R))
        ( subset-subsemiring-hom-large-poset-Subsemiring R)
        ( pullback-hom-large-poset-Subsemiring R S f))
```
