# Pullbacks of nonunital subsemirings

```agda
module ring-theory.pullbacks-nonunital-subsemirings where
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
open import ring-theory.poset-of-nonunital-subsemirings
open import ring-theory.semirings
open import ring-theory.nonunital-subsemirings
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
[nonunital subsemiring](ring-theory.nonunital-subsemirings.md) `K ≤ S`, the
{{concept "pullback" Disambiguation="nonunital subsemiring" Agda=pullback-Nonunital-Subsemiring}}
of `K` along `f` is defined by substituting `f` in `K`. In other
words, it is the nonunital subsemiring `f＊K` of `R` consisting of the elements
`x : R` such that `f x ∈ K`.

## Definitions

### The pullback of a nonunital subsemiring along a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S) (K : Nonunital-Subsemiring l3 S)
  where

  subset-pullback-Nonunital-Subsemiring : subset-Semiring l3 R
  subset-pullback-Nonunital-Subsemiring =
    subset-Nonunital-Subsemiring S K ∘ map-hom-Semiring R S f

  contains-zero-pullback-Nonunital-Subsemiring :
    contains-zero-subset-Semiring R subset-pullback-Nonunital-Subsemiring
  contains-zero-pullback-Nonunital-Subsemiring =
    is-closed-under-eq-Nonunital-Subsemiring' S K
      ( contains-zero-Nonunital-Subsemiring S K)
      ( preserves-zero-hom-Semiring R S f)

  is-closed-under-addition-pullback-Nonunital-Subsemiring :
    is-closed-under-addition-subset-Semiring R subset-pullback-Nonunital-Subsemiring
  is-closed-under-addition-pullback-Nonunital-Subsemiring p q =
    is-closed-under-eq-Nonunital-Subsemiring' S K
      ( is-closed-under-addition-Nonunital-Subsemiring S K p q)
      ( preserves-addition-hom-Semiring R S f)

  is-additive-submonoid-pullback-Nonunital-Subsemiring :
    is-additive-submonoid-subset-Semiring R subset-pullback-Nonunital-Subsemiring
  pr1 is-additive-submonoid-pullback-Nonunital-Subsemiring =
    contains-zero-pullback-Nonunital-Subsemiring
  pr2 is-additive-submonoid-pullback-Nonunital-Subsemiring =
    is-closed-under-addition-pullback-Nonunital-Subsemiring

  is-closed-under-multiplication-pullback-Nonunital-Subsemiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-pullback-Nonunital-Subsemiring
  is-closed-under-multiplication-pullback-Nonunital-Subsemiring p q =
    is-closed-under-eq-Nonunital-Subsemiring' S K
      ( is-closed-under-multiplication-Nonunital-Subsemiring S K p q)
      ( preserves-mul-hom-Semiring R S f)

  pullback-Nonunital-Subsemiring : Nonunital-Subsemiring l3 R
  pr1 pullback-Nonunital-Subsemiring =
    subset-pullback-Nonunital-Subsemiring
  pr1 (pr2 pullback-Nonunital-Subsemiring) =
    is-additive-submonoid-pullback-Nonunital-Subsemiring
  pr2 (pr2 pullback-Nonunital-Subsemiring) =
    is-closed-under-multiplication-pullback-Nonunital-Subsemiring

  is-in-pullback-Nonunital-Subsemiring : type-Semiring R → UU l3
  is-in-pullback-Nonunital-Subsemiring =
    is-in-Nonunital-Subsemiring R pullback-Nonunital-Subsemiring

  is-closed-under-eq-pullback-Nonunital-Subsemiring :
    {x y : type-Semiring R} →
    is-in-pullback-Nonunital-Subsemiring x → x ＝ y → is-in-pullback-Nonunital-Subsemiring y
  is-closed-under-eq-pullback-Nonunital-Subsemiring =
    is-closed-under-eq-Nonunital-Subsemiring R pullback-Nonunital-Subsemiring

  is-closed-under-eq-pullback-Nonunital-Subsemiring' :
    {x y : type-Semiring R} →
    is-in-pullback-Nonunital-Subsemiring y → x ＝ y → is-in-pullback-Nonunital-Subsemiring x
  is-closed-under-eq-pullback-Nonunital-Subsemiring' =
    is-closed-under-eq-Nonunital-Subsemiring' R pullback-Nonunital-Subsemiring
```

### The order preserving operation `pullback-Nonunital-Subsemiring`

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-pullback-Nonunital-Subsemiring :
    {l3 l4 : Level} (U : Nonunital-Subsemiring l3 S) (V : Nonunital-Subsemiring l4 S) →
    leq-Nonunital-Subsemiring S U V →
    leq-Nonunital-Subsemiring R
      ( pullback-Nonunital-Subsemiring R S f U)
      ( pullback-Nonunital-Subsemiring R S f V)
  preserves-order-pullback-Nonunital-Subsemiring U V =
    preserves-order-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-Nonunital-Subsemiring S U)
      ( subset-Nonunital-Subsemiring S V)

  pullback-hom-large-poset-Nonunital-Subsemiring :
    hom-Large-Poset
      ( λ l → l)
      ( Nonunital-Subsemiring-Large-Poset S)
      ( Nonunital-Subsemiring-Large-Poset R)
  map-hom-Large-Preorder pullback-hom-large-poset-Nonunital-Subsemiring =
    pullback-Nonunital-Subsemiring R S f
  preserves-order-hom-Large-Preorder pullback-hom-large-poset-Nonunital-Subsemiring =
    preserves-order-pullback-Nonunital-Subsemiring
```

## Properties

### The pullback operation commutes with the underlying subtype operation

The square

```text
                             pullback f
    Nonunital-Subsemiring S -----------> Nonunital-Subsemiring R
             |                                    |
      K ↦ UK |                                    | K ↦ UK
             |                                    |
             ∨                                    ∨
       subset-Semiring S -----------------> subset-Semiring R
                             pullback f
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.md)
by reflexivity.

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  coherence-square-pullback-subset-Nonunital-Subsemiring :
    coherence-square-hom-Large-Poset
      ( Nonunital-Subsemiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring S))
      ( Nonunital-Subsemiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
      ( pullback-hom-large-poset-Nonunital-Subsemiring R S f)
      ( subset-nonunital-subsemiring-hom-large-poset-Nonunital-Subsemiring S)
      ( subset-nonunital-subsemiring-hom-large-poset-Nonunital-Subsemiring R)
      ( pullback-subtype-hom-Large-Poset (map-hom-Semiring R S f))
  coherence-square-pullback-subset-Nonunital-Subsemiring =
    refl-sim-hom-Large-Poset
      ( Nonunital-Subsemiring-Large-Poset S)
      ( powerset-Large-Poset (type-Semiring R))
      ( comp-hom-Large-Poset
        ( Nonunital-Subsemiring-Large-Poset S)
        ( Nonunital-Subsemiring-Large-Poset R)
        ( powerset-Large-Poset (type-Semiring R))
        ( subset-nonunital-subsemiring-hom-large-poset-Nonunital-Subsemiring R)
        ( pullback-hom-large-poset-Nonunital-Subsemiring R S f))
```
