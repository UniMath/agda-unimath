# Linear spans in left modules over rings

```agda
module linear-algebra.linear-spans-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.cartesian-product-types

open import linear-algebra.left-modules-rings
open import linear-algebra.left-submodules-rings
open import linear-algebra.linear-combinations
open import linear-algebra.subsets-left-modules-rings

open import lists.concatenation-tuples
open import lists.functoriality-tuples
open import lists.tuples

open import ring-theory.rings
```

</details>

## Idea

Let `M` be a [left module](linear-algebra.left-modules-rings.md) over a
[ring](ring-theory.rings.md) `R` and `G` be a subset of `M`. The
{{#concept "linear span" Agda=is-linear-span-subset-left-module-prop-Ring Agda=linear-span-left-module-Ring}}
of `G` is the subset of `M` which contains all
[linear combinations](linear-algebra.linear-combinations.md) of the elements of
`G`.

## Definitions

### The condition of being a linear span

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (S : subset-left-module-Ring l3 R M)
  (G : subset-left-module-Ring l3 R M)
  where

  contains-all-linear-combinations-subset-left-module-prop-Ring :
    Prop (l1 ⊔ l2 ⊔ l3)
  contains-all-linear-combinations-subset-left-module-prop-Ring =
    Π-Prop
      ( ℕ)
      ( λ n →
        Π-Prop
          ( tuple (type-Ring R) n)
          ( λ scalars →
            Π-Prop
              ( tuple (type-subset-left-module-Ring R M G) n)
              ( λ vectors →
                S ( linear-combination-left-module-Ring R M
                    ( scalars)
                    ( map-tuple pr1 vectors)))))

  contains-all-linear-combinations-subset-left-module-Ring :
    UU (l1 ⊔ l2 ⊔ l3)
  contains-all-linear-combinations-subset-left-module-Ring =
    type-Prop
      contains-all-linear-combinations-subset-left-module-prop-Ring

  contains-only-linear-combinations-subset-left-module-prop-Ring :
    Prop (l1 ⊔ l2 ⊔ l3)
  contains-only-linear-combinations-subset-left-module-prop-Ring =
    Π-Prop
      ( type-subset-left-module-Ring R M S)
      ( λ x →
        exists-Prop
          ( ℕ)
          ( λ n →
            exists-Prop
              ( tuple (type-Ring R) n)
              ( λ scalars →
                exists-structure-Prop
                  ( tuple (type-subset-left-module-Ring R M G) n)
                  ( λ vectors →
                    pr1 x ＝
                    linear-combination-left-module-Ring R M
                      ( scalars)
                      ( map-tuple pr1 vectors)))))

  contains-only-linear-combinations-subset-left-module-Ring :
    UU (l1 ⊔ l2 ⊔ l3)
  contains-only-linear-combinations-subset-left-module-Ring =
    type-Prop
      contains-only-linear-combinations-subset-left-module-prop-Ring

  is-linear-span-subset-left-module-prop-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-linear-span-subset-left-module-prop-Ring =
    product-Prop
      contains-all-linear-combinations-subset-left-module-prop-Ring
      contains-only-linear-combinations-subset-left-module-prop-Ring

  is-linear-span-subset-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-linear-span-subset-left-module-Ring =
    type-Prop is-linear-span-subset-left-module-prop-Ring
```

### The type of linear spans

```agda
linear-span-left-module-Ring :
  {l1 l2 : Level}
  (l : Level)
  (R : Ring l1)
  (M : left-module-Ring l2 R) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
linear-span-left-module-Ring l R M =
  Σ ( (subset-left-module-Ring l R M) × (subset-left-module-Ring l R M))
    ( λ (S , G) → is-linear-span-subset-left-module-Ring R M S G)

module _
  {l1 l2 l3}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (S : linear-span-left-module-Ring l3 R M)
  where

  subset-linear-span-left-module-Ring : subset-left-module-Ring l3 R M
  subset-linear-span-left-module-Ring = pr1 (pr1 S)

  generators-linear-span-left-module-Ring : subset-left-module-Ring l3 R M
  generators-linear-span-left-module-Ring = pr2 (pr1 S)

  contains-all-linear-combinations-linear-span-left-module-Ring :
    contains-all-linear-combinations-subset-left-module-Ring R M
      subset-linear-span-left-module-Ring
      generators-linear-span-left-module-Ring
  contains-all-linear-combinations-linear-span-left-module-Ring =
    pr1 (pr2 S)

  contains-only-linear-combinations-linear-span-left-module-Ring :
    contains-only-linear-combinations-subset-left-module-Ring R M
      subset-linear-span-left-module-Ring
      generators-linear-span-left-module-Ring
  contains-only-linear-combinations-linear-span-left-module-Ring =
    pr2 (pr2 S)
```

## Properties

### Linear span has the structure of a submodule

```agda
module _
  {l1 l2 l3}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (S : linear-span-left-module-Ring l3 R M)
  where

  contains-zero-linear-span-left-module-Ring :
    contains-zero-subset-left-module-Ring R M
      ( subset-linear-span-left-module-Ring R M S)
  contains-zero-linear-span-left-module-Ring =
    contains-all-linear-combinations-linear-span-left-module-Ring R M S
      ( zero-ℕ)
      ( empty-tuple)
      ( empty-tuple)

  is-closed-under-addition-linear-span-left-module-Ring :
    is-closed-under-addition-subset-left-module-Ring R M
      ( subset-linear-span-left-module-Ring R M S)
  is-closed-under-addition-linear-span-left-module-Ring
    x y x-in-span y-in-span =
      let
        open
          do-syntax-trunc-Prop
            ( subset-linear-span-left-module-Ring R M S
              ( add-left-module-Ring R M x y))
      in
        do
          ( x-n , x-scalars-vectors-identity) ←
            contains-only-linear-combinations-linear-span-left-module-Ring R M S
              ( x , x-in-span)
          ( x-scalars , x-vectors-identity) ← x-scalars-vectors-identity
          ( x-vectors , x-identity) ← x-vectors-identity
          ( y-n , y-scalars-vectors-identity) ←
            contains-only-linear-combinations-linear-span-left-module-Ring R M S
              ( y , y-in-span)
          ( y-scalars , y-vectors-identity) ← y-scalars-vectors-identity
          ( y-vectors , y-identity) ← y-vectors-identity
          tr
            ( λ z → pr1 (subset-linear-span-left-module-Ring R M S z))
            ( equational-reasoning
              linear-combination-left-module-Ring R M
                ( concat-tuple x-scalars y-scalars)
                ( map-tuple pr1 (concat-tuple x-vectors y-vectors))
              ＝
                linear-combination-left-module-Ring R M
                  ( concat-tuple x-scalars y-scalars)
                  ( concat-tuple
                    ( map-tuple pr1 x-vectors)
                    ( map-tuple pr1 y-vectors))
                by ap
                  ( λ z →
                    ( linear-combination-left-module-Ring R M
                      ( concat-tuple x-scalars y-scalars)
                      ( z)))
                  ( distributive-map-concat-tuple pr1 x-vectors y-vectors)
              ＝
                add-left-module-Ring R M
                  ( linear-combination-left-module-Ring R M
                    ( x-scalars)
                    ( (map-tuple pr1 x-vectors)))
                  ( linear-combination-left-module-Ring R M
                    ( y-scalars)
                    ( (map-tuple pr1 y-vectors)))
                by
                  concatenation-is-addition-linear-combination-left-module-Ring
                    ( R)
                    ( M)
                    ( x-scalars)
                    ( map-tuple pr1 x-vectors)
                    ( y-scalars)
                    ( map-tuple pr1 y-vectors)
              ＝
                add-left-module-Ring R M
                  ( x)
                  ( linear-combination-left-module-Ring R M
                    ( y-scalars)
                    ( map-tuple pr1 y-vectors))
                by ap
                  ( λ z → add-left-module-Ring R M
                    ( z)
                    ( linear-combination-left-module-Ring R M
                      ( y-scalars)
                      ( map-tuple pr1 y-vectors)))
                  ( inv x-identity)
              ＝
                add-left-module-Ring R M x y
                by ap
                  ( λ z → add-left-module-Ring R M x z)
                  ( inv y-identity))
            ( contains-all-linear-combinations-linear-span-left-module-Ring
              ( R)
              ( M)
              ( S)
              ( y-n +ℕ x-n)
              ( concat-tuple x-scalars y-scalars)
              ( concat-tuple x-vectors y-vectors))

  is-closed-under-multiplication-by-scalar-linear-span-left-module-Ring :
    is-closed-under-multiplication-by-scalar-subset-left-module-Ring R M
      ( subset-linear-span-left-module-Ring R M S)
  is-closed-under-multiplication-by-scalar-linear-span-left-module-Ring
    r x x-in-span =
      let
        open
          do-syntax-trunc-Prop
            ( subset-linear-span-left-module-Ring R M S
              ( mul-left-module-Ring R M r x))
      in do
        ( n , scalars-vectors-identity) ←
          ( contains-only-linear-combinations-linear-span-left-module-Ring R M S
            ( x , x-in-span))
        ( scalars , scalars-vectors) ← scalars-vectors-identity
        ( vectors , identity) ← scalars-vectors
        ( tr
          ( λ y → pr1 (subset-linear-span-left-module-Ring R M S y))
          ( equational-reasoning
            linear-combination-left-module-Ring R M
              ( map-tuple (mul-Ring R r) scalars)
              ( map-tuple pr1 vectors)
            ＝
              mul-left-module-Ring R M
                ( r)
                ( linear-combination-left-module-Ring R M
                  ( scalars)
                  ( map-tuple pr1 vectors))
              by inv
                ( left-distributive-law-mul-linear-combination-left-module-Ring
                  ( R)
                  ( M)
                  ( r)
                  ( scalars)
                  ( map-tuple pr1 vectors))
            ＝
              mul-left-module-Ring R M r x
              by ap
                ( λ y → mul-left-module-Ring R M r y)
                ( inv identity))
          ( contains-all-linear-combinations-linear-span-left-module-Ring R M S
            ( n)
            ( map-tuple (mul-Ring R r) scalars)
            ( vectors)))

  left-submodule-linear-span-left-module-Ring : left-submodule-Ring l3 R M
  pr1 left-submodule-linear-span-left-module-Ring =
    subset-linear-span-left-module-Ring R M S
  pr1 (pr2 left-submodule-linear-span-left-module-Ring) =
    contains-zero-linear-span-left-module-Ring
  pr1 (pr2 (pr2 left-submodule-linear-span-left-module-Ring)) =
    is-closed-under-addition-linear-span-left-module-Ring
  pr2 (pr2 (pr2 left-submodule-linear-span-left-module-Ring)) =
    is-closed-under-multiplication-by-scalar-linear-span-left-module-Ring
```
