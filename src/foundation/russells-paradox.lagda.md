# Russell's paradox

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.russells-paradox where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.negation
open import foundation.small-types
open import foundation.small-universes
open import foundation.surjective-maps
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types

open import trees.multisets
open import trees.small-multisets
open import trees.universal-multiset
```

</details>

## Idea

Russell's paradox arises when a set of all sets is assumed to exist. In
Russell's paradox it is of no importance that the elementhood relation takes
values in propositions. In other words, Russell's paradox arises similarly if
there is a multiset of all multisets. We will construct Russell's paradox from
the assumption that a universe `U` is equivalent to a type `A : U`. We conclude
that there can be no universe that is contained in itself. Furthermore, using
replacement we show that for any type `A : U`, there is no surjective map
`A → U`.

## Definition

### Russell's multiset

```agda
Russell : (l : Level) → 𝕍 (lsuc l)
Russell l =
  comprehension-𝕍
    ( universal-multiset-𝕍 l)
    ( λ X → X ∉-𝕍 X)
```

## Properties

### If a universe is small with respect to another universe, then Russells multiset is also small

```agda
is-small-Russell :
  {l1 l2 : Level} → is-small-universe l2 l1 → is-small-𝕍 l2 (Russell l1)
is-small-Russell {l1} {l2} H =
  is-small-comprehension-𝕍 l2
    { lsuc l1}
    { universal-multiset-𝕍 l1}
    { λ z → z ∉-𝕍 z}
    ( is-small-universal-multiset-𝕍 l2 H)
    ( λ X → is-small-∉-𝕍 l2 {l1} {X} {X} (K X) (K X))
  where
  K = is-small-multiset-𝕍 (λ A → pr2 H A)

resize-Russell :
  {l1 l2 : Level} → is-small-universe l2 l1 → 𝕍 l2
resize-Russell {l1} {l2} H =
  resize-𝕍 (Russell l1) (is-small-Russell H)

is-small-resize-Russell :
  {l1 l2 : Level} (H : is-small-universe l2 l1) →
  is-small-𝕍 (lsuc l1) (resize-Russell H)
is-small-resize-Russell {l1} {l2} H =
  is-small-resize-𝕍 (Russell l1) (is-small-Russell H)

equiv-Russell-in-Russell :
  {l1 l2 : Level} (H : is-small-universe l2 l1) →
  (Russell l1 ∈-𝕍 Russell l1) ≃ (resize-Russell H ∈-𝕍 resize-Russell H)
equiv-Russell-in-Russell H =
  equiv-elementhood-resize-𝕍 (is-small-Russell H) (is-small-Russell H)
```

### Russell's paradox obtained from the assumption that `U` is `U`-small

```agda
paradox-Russell : {l : Level} → ¬ (is-small l (UU l))
paradox-Russell {l} H =
  no-fixed-points-neg
    ( R ∈-𝕍 R)
    ( pair (map-equiv β) (map-inv-equiv β))
  where

  K : is-small-universe l l
  K = pair H (λ X → pair X id-equiv)

  R : 𝕍 (lsuc l)
  R = Russell l

  is-small-R : is-small-𝕍 l R
  is-small-R = is-small-Russell K

  R' : 𝕍 l
  R' = resize-Russell K

  is-small-R' : is-small-𝕍 (lsuc l) R'
  is-small-R' = is-small-resize-Russell K

  abstract
    p : resize-𝕍 R' is-small-R' ＝ R
    p = resize-resize-𝕍 is-small-R

  α : (R ∈-𝕍 R) ≃ (R' ∈-𝕍 R')
  α = equiv-Russell-in-Russell K

  abstract
    β : (R ∈-𝕍 R) ≃ (R ∉-𝕍 R)
    β = ( equiv-precomp α empty) ∘e
        ( ( left-unit-law-Σ-is-contr
            { B = λ t → (pr1 t) ∉-𝕍 (pr1 t)}
            ( is-torsorial-path' R')
            ( pair R' refl)) ∘e
          ( ( inv-associative-Σ (𝕍 l) (_＝ R') (λ t → (pr1 t) ∉-𝕍 (pr1 t))) ∘e
            ( ( equiv-tot
                ( λ t →
                  ( commutative-prod) ∘e
                  ( equiv-prod
                    ( id-equiv)
                    ( inv-equiv
                      ( ( equiv-concat'
                          _ ( p)) ∘e
                        ( eq-resize-𝕍
                          ( is-small-multiset-𝕍 is-small-lsuc t)
                          ( is-small-R'))))))) ∘e
              ( associative-Σ
                ( 𝕍 l)
                ( λ t → t ∉-𝕍 t)
                ( λ t → ( resize-𝕍
                          ( pr1 t)
                          ( is-small-multiset-𝕍 is-small-lsuc (pr1 t))) ＝
                        ( R))))))
```

### There can be no surjective map `f : A → U` for any `A : U`

```agda
no-surjection-onto-universe :
  {l : Level} {A : UU l} (f : A → UU l) → ¬ (is-surjective f)
no-surjection-onto-universe f H =
  paradox-Russell
    ( is-small-is-surjective H
      ( is-small')
      ( is-locally-small-UU))
```
