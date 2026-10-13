# Alternating multilinear maps on left modules over commutative rings

```agda
module linear-algebra.alternating-multilinear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.negated-equality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.alternating-bilinear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.multilinear-maps-left-modules-commutative-rings

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given two [left modules](linear-algebra.left-modules-commutative-rings.md) `M`
and `N` over a [commutative ring](commutative-algebra.commutative-rings.md), and
a [natural number](elementary-number-theory.natural-numbers.md) `k`, a
[multilinear map](linear-algebra.multilinear-maps-left-modules-commutative-rings.md)
`f : M → N` is
{{#concept "alternating" Disambiguation="multilinear map on left modules over commutative rings" Agda=is-alternating-multilinear-map-left-module-Commutative-Ring}}
if for any distinct `i` and `j` in `Fin k`, and `u : Mᵏ`, if `uᵢ = uⱼ`, then
`f u = 0`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (n : ℕ)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  is-alternating-prop-multilinear-map-left-module-Commutative-Ring :
    subtype
      ( l2 ⊔ l3)
      ( multilinear-map-left-module-Commutative-Ring R n M N)
  is-alternating-prop-multilinear-map-left-module-Commutative-Ring f =
    Π-Prop
      ( Fin n)
      ( λ i →
        Π-Prop
          ( Fin n)
          ( λ j →
            Π-Prop
              ( i ≠ j)
              ( λ i≠j →
                Π-Prop
                  ( fin-sequence (type-left-module-Commutative-Ring R M) n)
                  ( λ u →
                    hom-Prop
                      ( Id-Prop
                        ( set-left-module-Commutative-Ring R M)
                        ( u i)
                        ( u j))
                      ( is-zero-prop-left-module-Commutative-Ring
                        ( R)
                        ( N)
                        ( map-multilinear-map-left-module-Commutative-Ring
                          ( R)
                          ( n)
                          ( M)
                          ( N)
                          ( f)
                          ( u)))))))

  is-alternating-multilinear-map-left-module-Commutative-Ring :
    multilinear-map-left-module-Commutative-Ring R n M N → UU (l2 ⊔ l3)
  is-alternating-multilinear-map-left-module-Commutative-Ring =
    is-in-subtype
      ( is-alternating-prop-multilinear-map-left-module-Commutative-Ring)

  alternating-multilinear-map-left-module-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3)
  alternating-multilinear-map-left-module-Commutative-Ring =
    type-subtype
      ( is-alternating-prop-multilinear-map-left-module-Commutative-Ring)

  map-alternating-multilinear-map-left-module-Commutative-Ring :
    alternating-multilinear-map-left-module-Commutative-Ring →
    fin-sequence (type-left-module-Commutative-Ring R M) n →
    type-left-module-Commutative-Ring R N
  map-alternating-multilinear-map-left-module-Commutative-Ring ((f , _) , _) = f
```
