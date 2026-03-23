# Multilinear maps between left modules over rings

```agda
module multilinear-algebra.multilinear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import lists.finite-sequences

open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Let `M` and `N` be two [left modules](linear-algebra.left-modules-rings.md) over
a [ring](ring-theory.rings.md) `R` and `n : ℕ` a
[natural number](elementary-number-theory.natural-numbers.md); a map from the
type of [finite sequences](lists.finite-sequences.md) of `M` into `N`,
`f : Mⁿ⁺¹ → N` is called
{{#concept "multilinear" Disambiguation="map between left modules over a ring" Agda=is-multilinear-map-left-module-Ring WD="multilinear map" WDID=Q1952404}}
if, for any [index](univalent-combinatorics.standard-finite-types.md) `i : ℕₙ`
and any element `(u₀,...,uᵢ₋₁,uᵢ₊₁,...,uₙ) : Mⁿ`, the map

```text
x ↦ f (u₀,...,uᵢ₋₁,x,uᵢ₊₁,...,uₙ)
```

is [linear](linear-algebra.linear-maps-left-modules-rings.md).

## Definitions

### Multilinear maps between modules over a ring

```agda
module _
  {l1 l2 l3 : Level}
  ( R : Ring l1)
  ( M : left-module-Ring l2 R)
  ( N : left-module-Ring l3 R)
  ( n : ℕ)
  ( f :
    fin-sequence (type-left-module-Ring R M) (succ-ℕ n) →
    type-left-module-Ring R N)
  where

  is-multilinear-map-prop-left-module-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-multilinear-map-prop-left-module-Ring =
    Π-Prop
      ( Fin (succ-ℕ n))
      ( λ i →
        Π-Prop
          ( fin-sequence (type-left-module-Ring R M) n)
          ( λ u →
            is-linear-map-prop-left-module-Ring
              ( R)
              ( M)
              ( N)
              ( λ x → f ( insert-at-fin-sequence n x i u))))

  is-multilinear-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-multilinear-map-left-module-Ring =
    type-Prop is-multilinear-map-prop-left-module-Ring

  is-prop-is-multilinear-map-left-module-Ring :
    is-prop is-multilinear-map-left-module-Ring
  is-prop-is-multilinear-map-left-module-Ring =
    is-prop-type-Prop is-multilinear-map-prop-left-module-Ring
```

### The type of multilinear maps between left modules

```agda
multilinear-map-left-module-Ring :
  {l1 l2 l3 : Level} →
  (R : Ring l1) →
  (M : left-module-Ring l2 R) →
  (N : left-module-Ring l3 R) →
  (n : ℕ) →
  UU (l1 ⊔ l2 ⊔ l3)
multilinear-map-left-module-Ring R M N n =
  type-subtype
    ( is-multilinear-map-prop-left-module-Ring R M N n)

module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (n : ℕ)
  (f : multilinear-map-left-module-Ring R M N n)
  where

  map-multilinear-map-left-module-Ring :
    fin-sequence (type-left-module-Ring R M) (succ-ℕ n) →
    type-left-module-Ring R N
  map-multilinear-map-left-module-Ring = pr1 f

  is-multilinear-map-multilinear-map-left-module-Ring :
    is-multilinear-map-left-module-Ring R M N n
      map-multilinear-map-left-module-Ring
  is-multilinear-map-multilinear-map-left-module-Ring = pr2 f
```

## External links

- [multilinear maps](https://ncatlab.org/nlab/show/multilinear+map) at $n$Lab
- [Multilinear maps](https://en.wikipedia.org/wiki/Multilinear_map) at Wikipedia
