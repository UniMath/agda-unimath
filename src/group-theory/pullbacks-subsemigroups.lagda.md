# Pullbacks of subsemigroups

```agda
module group-theory.pullbacks-subsemigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
open import group-theory.subsemigroups
open import group-theory.subsets-semigroups
```

</details>

## Idea

Given a [semigroup homomorphism](group-theory.homomorphisms-semigroups.md) `f : G → H` into a [semigroup](group-theory.semigroups.md) `H` equipped with a [subsemigroup](group-theory.subsemigroups.md) `K ≤ H`, the **pullback** `f∗K` of `K` along `f` is defined by substituting `f` in `K`. In other words, it is the subsemigroup `f∗K` of `G` consisting of the elements `x : G` such that `f x ∈ K`.

## Definitions

### The pullback of a subsemigroup along a semigroup homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H) (K : Subsemigroup l3 H)
  where

  subset-pullback-Subsemigroup : subset-Semigroup l3 G
  subset-pullback-Subsemigroup =
    subset-Subsemigroup H K ∘ map-hom-Semigroup G H f

  is-closed-under-multiplication-pullback-Subsemigroup :
    is-closed-under-multiplication-subset-Semigroup G
      subset-pullback-Subsemigroup
  is-closed-under-multiplication-pullback-Subsemigroup p q =
    is-closed-under-eq-Subsemigroup' H K
      ( is-closed-under-multiplication-Subsemigroup H K p q)
      ( preserves-mul-hom-Semigroup G H f)

  pullback-Subsemigroup : Subsemigroup l3 G
  pr1 pullback-Subsemigroup =
    subset-pullback-Subsemigroup
  pr2 pullback-Subsemigroup =
    is-closed-under-multiplication-pullback-Subsemigroup

  is-in-pullback-Subsemigroup : type-Semigroup G → UU l3
  is-in-pullback-Subsemigroup =
    is-in-Subsemigroup G pullback-Subsemigroup

  is-closed-under-eq-pullback-Subsemigroup :
    {x y : type-Semigroup G} →
    is-in-pullback-Subsemigroup x → x ＝ y → is-in-pullback-Subsemigroup y
  is-closed-under-eq-pullback-Subsemigroup =
    is-closed-under-eq-Subsemigroup G pullback-Subsemigroup

  is-closed-under-eq-pullback-Subsemigroup' :
    {x y : type-Semigroup G} →
    is-in-pullback-Subsemigroup y → x ＝ y → is-in-pullback-Subsemigroup x
  is-closed-under-eq-pullback-Subsemigroup' =
    is-closed-under-eq-Subsemigroup' G pullback-Subsemigroup
```
