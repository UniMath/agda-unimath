# Iterated cartesian products of higher groups

```agda
module higher-group-theory.iterated-cartesian-products-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.iterated-cartesian-product-types
open import foundation.mere-equality
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import higher-group-theory.cartesian-products-higher-groups
open import higher-group-theory.higher-groups
open import higher-group-theory.trivial-higher-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The iterated Cartesian product of a family of `∞-Group` over `Fin n` is defined
recursively on `Fin n`.

## Definition

```agda
iterated-product-∞-Group :
  {l : Level} (n : ℕ) (G : Fin n → (∞-Group l)) → ∞-Group l
iterated-product-∞-Group zero-ℕ G = trivial-∞-Group
iterated-product-∞-Group (succ-ℕ n) G =
  product-∞-Group
    ( G (inr star))
    ( iterated-product-∞-Group n (G ∘ inl))

module _
  {l : Level} (n : ℕ) (G : Fin n → ∞-Group l)
  where

  classifying-pointed-type-iterated-product-∞-Group :
    Pointed-Type l
  classifying-pointed-type-iterated-product-∞-Group =
    pr1 (iterated-product-∞-Group n G)

  classifying-type-iterated-product-∞-Group : UU l
  classifying-type-iterated-product-∞-Group =
    type-Pointed-Type
      classifying-pointed-type-iterated-product-∞-Group

  shape-iterated-product-∞-Group :
    classifying-type-iterated-product-∞-Group
  shape-iterated-product-∞-Group =
    point-Pointed-Type
      classifying-pointed-type-iterated-product-∞-Group

  is-0-connected-classifying-type-iterated-product-∞-Group :
    is-0-connected classifying-type-iterated-product-∞-Group
  is-0-connected-classifying-type-iterated-product-∞-Group =
    pr2 (iterated-product-∞-Group n G)

  mere-eq-classifying-type-iterated-product-∞-Group :
    (X Y : classifying-type-iterated-product-∞-Group) →
    mere-eq X Y
  mere-eq-classifying-type-iterated-product-∞-Group =
    mere-eq-is-0-connected
      is-0-connected-classifying-type-iterated-product-∞-Group

  elim-prop-classifying-type-iterated-product-∞-Group :
    {l2 : Level}
    (P : classifying-type-iterated-product-∞-Group → Prop l2) →
    type-Prop (P shape-iterated-product-∞-Group) →
    ((X : classifying-type-iterated-product-∞-Group) →
    type-Prop (P X))
  elim-prop-classifying-type-iterated-product-∞-Group =
    apply-dependent-universal-property-is-0-connected
      shape-iterated-product-∞-Group
      is-0-connected-classifying-type-iterated-product-∞-Group

  type-iterated-product-∞-Group : UU (l)
  type-iterated-product-∞-Group =
    type-Ω classifying-pointed-type-iterated-product-∞-Group

  unit-iterated-product-∞-Group :
    type-iterated-product-∞-Group
  unit-iterated-product-∞-Group =
    refl-Ω classifying-pointed-type-iterated-product-∞-Group

  mul-iterated-product-∞-Group :
    (x y : type-iterated-product-∞-Group) →
    type-iterated-product-∞-Group
  mul-iterated-product-∞-Group =
    mul-Ω classifying-pointed-type-iterated-product-∞-Group

  assoc-mul-iterated-product-∞-Group :
    (x y z : type-iterated-product-∞-Group) →
    mul-iterated-product-∞-Group (mul-iterated-product-∞-Group x y) z ＝
    mul-iterated-product-∞-Group x (mul-iterated-product-∞-Group y z)
  assoc-mul-iterated-product-∞-Group =
    associative-mul-Ω
      classifying-pointed-type-iterated-product-∞-Group

  left-unit-law-mul-iterated-product-∞-Group :
    (x : type-iterated-product-∞-Group) →
    mul-iterated-product-∞-Group unit-iterated-product-∞-Group x ＝ x
  left-unit-law-mul-iterated-product-∞-Group =
    left-unit-law-mul-Ω
      classifying-pointed-type-iterated-product-∞-Group

  right-unit-law-mul-iterated-product-∞-Group :
    (y : type-iterated-product-∞-Group) →
    mul-iterated-product-∞-Group y unit-iterated-product-∞-Group ＝ y
  right-unit-law-mul-iterated-product-∞-Group =
    right-unit-law-mul-Ω
      classifying-pointed-type-iterated-product-∞-Group

  coherence-unit-laws-mul-iterated-product-∞-Group :
    left-unit-law-mul-iterated-product-∞-Group unit-iterated-product-∞-Group ＝
    right-unit-law-mul-iterated-product-∞-Group unit-iterated-product-∞-Group
  coherence-unit-laws-mul-iterated-product-∞-Group = refl

  inv-iterated-product-∞-Group :
    type-iterated-product-∞-Group → type-iterated-product-∞-Group
  inv-iterated-product-∞-Group =
    inv-Ω classifying-pointed-type-iterated-product-∞-Group

  left-inverse-law-mul-iterated-product-∞-Group :
    (x : type-iterated-product-∞-Group) →
    mul-iterated-product-∞-Group (inv-iterated-product-∞-Group x) x ＝
    unit-iterated-product-∞-Group
  left-inverse-law-mul-iterated-product-∞-Group =
    left-inverse-law-mul-Ω
      classifying-pointed-type-iterated-product-∞-Group

  right-inverse-law-mul-iterated-product-∞-Group :
    (x : type-iterated-product-∞-Group) →
    mul-iterated-product-∞-Group x (inv-iterated-product-∞-Group x) ＝
    unit-iterated-product-∞-Group
  right-inverse-law-mul-iterated-product-∞-Group =
    right-inverse-law-mul-Ω
      classifying-pointed-type-iterated-product-∞-Group
```

## Properties

### The `type-∞-Group` of a iterated product of a `∞-Group` is the iterated product of the `type-∞-Group`

```agda
equiv-type-∞-Group-iterated-product-∞-Group :
  {l : Level} (n : ℕ) (G : Fin n → ∞-Group l) →
  ( type-iterated-product-∞-Group n G) ≃
  ( iterated-product-Fin-recursive n (type-∞-Group ∘ G))
equiv-type-∞-Group-iterated-product-∞-Group zero-ℕ G =
  equiv-is-contr
    ( is-proof-irrelevant-is-prop
        ( is-set-is-contr is-contr-raise-unit raise-star raise-star) refl)
    is-contr-raise-unit
equiv-type-∞-Group-iterated-product-∞-Group (succ-ℕ n) G =
  ( ( equiv-product
        ( id-equiv)
        ( equiv-type-∞-Group-iterated-product-∞-Group
            ( n)
            (G ∘ inl))) ∘e
    ( ( equiv-type-∞-Group-product-∞-Group
          ( G (inr star))
          ( iterated-product-∞-Group n (G ∘ inl)))))
```
