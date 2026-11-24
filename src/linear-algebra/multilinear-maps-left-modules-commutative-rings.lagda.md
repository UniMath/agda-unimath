# Multilinear maps on left modules over commutative rings

```agda
module linear-algebra.multilinear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.bilinear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings

open import lists.finite-sequences
open import lists.finite-sequences-of-types
open import lists.insert-at-index-finite-sequences-of-types
open import lists.remove-at-index-finite-sequences
open import lists.replace-at-index-finite-sequences-of-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [finite sequence](lists.finite-sequences.md) of
[left modules](linear-algebra.left-modules-commutative-rings.md) `Mᵢ` over a
[commutative ring](commutative-algebra.commutative-rings.md) `R`, and a left
module `N` over `R`, a
{{#concept "multilinear map" Disambiguation="on left modules over a commutative ring" Agda=multilinear-map-fin-sequence-left-module-Commutative-Ring}}
from the `Mᵢ` to the `N` is a function `f : Π Mᵢ → N` that is
[linear](linear-algebra.linear-maps-left-modules-commutative-rings.md) in each
coordinate.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (n : ℕ)
  (M : fin-sequence (left-module-Commutative-Ring l2 R) n)
  where

  Π-fin-sequence-type-left-module-Commutative-Ring : UU l2
  Π-fin-sequence-type-left-module-Commutative-Ring =
    Π-fin-sequence n (type-left-module-Commutative-Ring R ∘ M)

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (n : ℕ)
  (M : fin-sequence (left-module-Commutative-Ring l2 R) n)
  (N : left-module-Commutative-Ring l3 R)
  where

  map-fin-sequence-left-module-Commutative-Ring : UU (l2 ⊔ l3)
  map-fin-sequence-left-module-Commutative-Ring =
    Π-fin-sequence-type-left-module-Commutative-Ring R n M →
    type-left-module-Commutative-Ring R N

is-linear-in-coordinate-prop-map-fin-sequence-left-module-Commutative-Ring :
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (n : ℕ)
  (M : fin-sequence (left-module-Commutative-Ring l2 R) n)
  (N : left-module-Commutative-Ring l3 R) →
  map-fin-sequence-left-module-Commutative-Ring R n M N →
  Fin n → Prop (l1 ⊔ l2 ⊔ l3)
is-linear-in-coordinate-prop-map-fin-sequence-left-module-Commutative-Ring
  R (succ-ℕ n) M N f i =
  Π-Prop
    ( Π-fin-sequence-type-left-module-Commutative-Ring
      ( R)
      ( n)
      ( remove-at-fin-sequence n i M))
    ( λ u →
      is-linear-map-prop-left-module-Commutative-Ring
        ( R)
        ( M i)
        ( N)
        ( λ mᵢ →
          f ( insert-at-Π-fin-sequence
              ( n)
              ( type-left-module-Commutative-Ring R ∘ M)
              ( i)
              ( mᵢ)
              ( u))))

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (n : ℕ)
  (M : fin-sequence (left-module-Commutative-Ring l2 R) n)
  (N : left-module-Commutative-Ring l3 R)
  where

  is-multilinear-prop-map-fin-sequence-left-module-Commutative-Ring :
    subtype
      ( l1 ⊔ l2 ⊔ l3)
      ( map-fin-sequence-left-module-Commutative-Ring R n M N)
  is-multilinear-prop-map-fin-sequence-left-module-Commutative-Ring f =
    Π-Prop
      ( Fin n)
      ( is-linear-in-coordinate-prop-map-fin-sequence-left-module-Commutative-Ring
        ( R)
        ( n)
        ( M)
        ( N)
        ( f))

  is-multilinear-map-fin-sequence-left-module-Commutative-Ring :
    map-fin-sequence-left-module-Commutative-Ring R n M N → UU (l1 ⊔ l2 ⊔ l3)
  is-multilinear-map-fin-sequence-left-module-Commutative-Ring =
    is-in-subtype
      ( is-multilinear-prop-map-fin-sequence-left-module-Commutative-Ring)

  multilinear-map-fin-sequence-left-module-Commutative-Ring :
    UU (l1 ⊔ l2 ⊔ l3)
  multilinear-map-fin-sequence-left-module-Commutative-Ring =
    type-subtype
      ( is-multilinear-prop-map-fin-sequence-left-module-Commutative-Ring)

  map-multilinear-map-fin-sequence-left-module-Commutative-Ring :
    multilinear-map-fin-sequence-left-module-Commutative-Ring →
    Π-fin-sequence-type-left-module-Commutative-Ring R n M →
    type-left-module-Commutative-Ring R N
  map-multilinear-map-fin-sequence-left-module-Commutative-Ring = pr1

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (n : ℕ)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  is-multilinear-prop-map-left-module-Commutative-Ring :
    subtype
      ( l1 ⊔ l2 ⊔ l3)
      ( fin-sequence (type-left-module-Commutative-Ring R M) n →
        type-left-module-Commutative-Ring R N)
  is-multilinear-prop-map-left-module-Commutative-Ring =
    is-multilinear-prop-map-fin-sequence-left-module-Commutative-Ring
      ( R)
      ( n)
      ( λ _ → M)
      ( N)

  is-multilinear-map-left-module-Commutative-Ring :
    ( fin-sequence (type-left-module-Commutative-Ring R M) n →
      type-left-module-Commutative-Ring R N) →
    UU (l1 ⊔ l2 ⊔ l3)
  is-multilinear-map-left-module-Commutative-Ring =
    is-in-subtype is-multilinear-prop-map-left-module-Commutative-Ring

  multilinear-map-left-module-Commutative-Ring :
    UU (l1 ⊔ l2 ⊔ l3)
  multilinear-map-left-module-Commutative-Ring =
    type-subtype is-multilinear-prop-map-left-module-Commutative-Ring

  map-multilinear-map-left-module-Commutative-Ring :
    multilinear-map-left-module-Commutative-Ring →
    fin-sequence (type-left-module-Commutative-Ring R M) n →
    type-left-module-Commutative-Ring R N
  map-multilinear-map-left-module-Commutative-Ring = pr1
```

## Properties

### Linear maps in each coordinate from multilinear maps

```agda
map-linear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring :
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (n : ℕ)
  (M : fin-sequence (left-module-Commutative-Ring l2 R) (succ-ℕ n))
  (N : left-module-Commutative-Ring l3 R) →
  multilinear-map-fin-sequence-left-module-Commutative-Ring R (succ-ℕ n) M N →
  (i : Fin (succ-ℕ n)) →
  Π-fin-sequence-type-left-module-Commutative-Ring
    ( R)
    ( n)
    ( remove-at-fin-sequence n i M) →
  type-left-module-Commutative-Ring R (M i) →
  type-left-module-Commutative-Ring R N
map-linear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring
  R n M N (f , ml-f) i u mᵢ =
  f ( insert-at-Π-fin-sequence
      ( n)
      ( type-left-module-Commutative-Ring R ∘ M)
      ( i)
      ( mᵢ)
      ( u))

linear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring :
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (n : ℕ)
  (M : fin-sequence (left-module-Commutative-Ring l2 R) (succ-ℕ n))
  (N : left-module-Commutative-Ring l3 R) →
  multilinear-map-fin-sequence-left-module-Commutative-Ring R (succ-ℕ n) M N →
  (i : Fin (succ-ℕ n)) →
  Π-fin-sequence-type-left-module-Commutative-Ring
    ( R)
    ( n)
    ( remove-at-fin-sequence n i M) →
  linear-map-left-module-Commutative-Ring R (M i) N
linear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring
  R n M N mlf@(f , is-ml-f) i u =
  ( map-linear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring
      ( R)
      ( n)
      ( M)
      ( N)
      ( mlf)
      ( i)
      ( u) ,
    is-ml-f i u)
```

### Bilinear maps in a pair of coordinates from multilinear maps

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (n : ℕ)
  (M : fin-sequence (left-module-Commutative-Ring l2 R) (n +ℕ 2))
  (N : left-module-Commutative-Ring l3 R)
  (mlf@(f , is-ml-f) :
    multilinear-map-fin-sequence-left-module-Commutative-Ring R (n +ℕ 2) M N)
  (i j : Fin (n +ℕ 2))
  (i≠j : i ≠ j)
  (u :
    Π-fin-sequence-type-left-module-Commutative-Ring
      ( R)
      ( n)
      ( remove-at-two-indices-fin-sequence n i j i≠j M))
  (let
    u' =
      insert-at-two-indices-Π-fin-sequence
        ( n)
        ( type-left-module-Commutative-Ring R ∘ M)
        ( i)
        ( j)
        ( i≠j)
        ( zero-left-module-Commutative-Ring R (M i))
        ( zero-left-module-Commutative-Ring R (M j))
        ( u))
  where

  coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring R (M i) →
    type-left-module-Commutative-Ring R (M j) →
    Π-fin-sequence-type-left-module-Commutative-Ring R (n +ℕ 2) M
  coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring
    mᵢ mⱼ =
    replace-at-Π-fin-sequence
      ( succ-ℕ n)
      ( type-left-module-Commutative-Ring R ∘ M)
      ( i)
      ( mᵢ)
      ( replace-at-Π-fin-sequence
        ( succ-ℕ n)
        ( type-left-module-Commutative-Ring R ∘ M)
        ( j)
        ( mⱼ)
        ( u'))

  coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring' :
    type-left-module-Commutative-Ring R (M i) →
    type-left-module-Commutative-Ring R (M j) →
    Π-fin-sequence-type-left-module-Commutative-Ring R (n +ℕ 2) M
  coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
    mᵢ mⱼ =
    replace-at-Π-fin-sequence
      ( succ-ℕ n)
      ( type-left-module-Commutative-Ring R ∘ M)
      ( j)
      ( mⱼ)
      ( replace-at-Π-fin-sequence
        ( succ-ℕ n)
        ( type-left-module-Commutative-Ring R ∘ M)
        ( i)
        ( mᵢ)
        ( u'))

  abstract
    htpy-coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring' :
      (mᵢ : type-left-module-Commutative-Ring R (M i))
      (mⱼ : type-left-module-Commutative-Ring R (M j)) →
      coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring
        ( mᵢ)
        ( mⱼ) ~
      coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
        ( mᵢ)
        ( mⱼ)
    htpy-coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
      mᵢ mⱼ =
      htpy-swap-replace-at-Π-fin-sequence
        ( n)
        ( type-left-module-Commutative-Ring R ∘ M)
        ( i)
        ( j)
        ( i≠j)
        ( mᵢ)
        ( mⱼ)
        ( u')

    binary-htpy-coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring' :
      binary-htpy
        ( coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring)
        ( coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring')
    binary-htpy-coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
      mᵢ mⱼ =
      eq-htpy
        ( htpy-coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
          ( mᵢ)
          ( mⱼ))

  map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring R (M i) →
    type-left-module-Commutative-Ring R (M j) →
    type-left-module-Commutative-Ring R N
  map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring
    mᵢ mⱼ =
    f
      ( coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring
        ( mᵢ)
        ( mⱼ))

  map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring' :
    type-left-module-Commutative-Ring R (M i) →
    type-left-module-Commutative-Ring R (M j) →
    type-left-module-Commutative-Ring R N
  map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
    mᵢ mⱼ =
    f
      ( coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
        ( mᵢ)
        ( mⱼ))

  abstract
    binary-htpy-map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring' :
      binary-htpy
        ( map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring)
        ( map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring')
    binary-htpy-map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
      mᵢ mⱼ =
      ap
        ( f)
        ( binary-htpy-coordinates-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
          ( mᵢ)
          ( mⱼ))

    is-linear-on-left-map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring :
      is-linear-on-left-binary-map-left-module-Commutative-Ring
        ( R)
        ( M i)
        ( M j)
        ( N)
        ( map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring)
    is-linear-on-left-map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring
      mⱼ =
      is-ml-f i _

    is-linear-on-right-map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring :
      is-linear-on-right-binary-map-left-module-Commutative-Ring
        ( R)
        ( M i)
        ( M j)
        ( N)
        ( map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring)
    is-linear-on-right-map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring
      mᵢ =
      inv-tr
        ( is-linear-map-left-module-Commutative-Ring R (M j) N)
        ( eq-htpy
          ( binary-htpy-map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring'
            ( mᵢ)))
        ( is-ml-f j _)

  bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring :
    bilinear-map-left-module-Commutative-Ring R (M i) (M j) N
  bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring =
    ( map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring ,
      is-linear-on-left-map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring ,
      is-linear-on-right-map-bilinear-map-multilinear-map-fin-sequence-left-module-Commutative-Ring)
```
