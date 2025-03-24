# Iterated cartesian products of concrete groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.iterated-cartesian-products-concrete-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types funext univalence truncations
open import foundation.1-types funext univalence
open import foundation.contractible-types funext univalence
open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.dependent-products-propositions funext
open import foundation.dependent-products-truncated-types funext
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.functoriality-cartesian-product-types funext
open import foundation.identity-types funext
open import foundation.iterated-cartesian-product-types funext univalence truncations
open import foundation.mere-equality funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.propositions funext univalence
open import foundation.raising-universe-levels-unit-type
open import foundation.sets funext univalence
open import foundation.truncated-types funext univalence
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.cartesian-products-concrete-groups funext univalence truncations
open import group-theory.concrete-groups funext univalence truncations
open import group-theory.groups funext univalence truncations
open import group-theory.trivial-concrete-groups funext univalence truncations

open import higher-group-theory.higher-groups funext univalence truncations

open import structured-types.pointed-types

open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

The iterated Cartesian product of a family of `Concrete-Group` over `Fin n` is
defined recursively on `Fin n`.

## Definition

```agda
iterated-product-Concrete-Group :
  {l : Level} (n : ℕ) (G : Fin n → Concrete-Group l) →
  Concrete-Group l
iterated-product-Concrete-Group zero-ℕ G = trivial-Concrete-Group
iterated-product-Concrete-Group (succ-ℕ n) G =
  product-Concrete-Group
    ( G (inr star))
    ( iterated-product-Concrete-Group n (G ∘ inl))

module _
  {l : Level} (n : ℕ) (G : Fin n → Concrete-Group l)
  where

  ∞-group-iterated-product-Concrete-Group : ∞-Group l
  ∞-group-iterated-product-Concrete-Group =
    pr1 (iterated-product-Concrete-Group n G)

  classifying-pointed-type-iterated-product-Concrete-Group : Pointed-Type l
  classifying-pointed-type-iterated-product-Concrete-Group =
    classifying-pointed-type-∞-Group ∞-group-iterated-product-Concrete-Group

  classifying-type-iterated-product-Concrete-Group : UU l
  classifying-type-iterated-product-Concrete-Group =
    classifying-type-∞-Group ∞-group-iterated-product-Concrete-Group

  shape-iterated-product-Concrete-Group :
    classifying-type-iterated-product-Concrete-Group
  shape-iterated-product-Concrete-Group =
    shape-∞-Group ∞-group-iterated-product-Concrete-Group

  is-0-connected-classifying-type-iterated-product-Concrete-Group :
    is-0-connected classifying-type-iterated-product-Concrete-Group
  is-0-connected-classifying-type-iterated-product-Concrete-Group =
    is-0-connected-classifying-type-∞-Group
      ∞-group-iterated-product-Concrete-Group

  mere-eq-classifying-type-iterated-product-Concrete-Group :
    (X Y : classifying-type-iterated-product-Concrete-Group) → mere-eq X Y
  mere-eq-classifying-type-iterated-product-Concrete-Group =
    mere-eq-classifying-type-∞-Group ∞-group-iterated-product-Concrete-Group

  elim-prop-classifying-type-iterated-product-Concrete-Group :
    {l2 : Level}
    (P : classifying-type-iterated-product-Concrete-Group → Prop l2) →
    type-Prop (P shape-iterated-product-Concrete-Group) →
    ((X : classifying-type-iterated-product-Concrete-Group) → type-Prop (P X))
  elim-prop-classifying-type-iterated-product-Concrete-Group =
    elim-prop-classifying-type-∞-Group ∞-group-iterated-product-Concrete-Group

  type-iterated-product-Concrete-Group : UU l
  type-iterated-product-Concrete-Group =
    type-∞-Group ∞-group-iterated-product-Concrete-Group

  is-set-type-iterated-product-Concrete-Group :
    is-set type-iterated-product-Concrete-Group
  is-set-type-iterated-product-Concrete-Group =
    pr2 (iterated-product-Concrete-Group n G)

  set-iterated-product-Concrete-Group : Set l
  set-iterated-product-Concrete-Group =
    type-iterated-product-Concrete-Group ,
    is-set-type-iterated-product-Concrete-Group

  abstract
    is-1-type-classifying-type-iterated-product-Concrete-Group :
      is-trunc one-𝕋 classifying-type-iterated-product-Concrete-Group
    is-1-type-classifying-type-iterated-product-Concrete-Group X Y =
      apply-universal-property-trunc-Prop
        ( mere-eq-classifying-type-iterated-product-Concrete-Group
            shape-iterated-product-Concrete-Group
            X)
        ( is-set-Prop (Id X Y))
        ( λ where
          refl →
            apply-universal-property-trunc-Prop
              ( mere-eq-classifying-type-iterated-product-Concrete-Group
                  shape-iterated-product-Concrete-Group
                  Y)
              ( is-set-Prop (Id shape-iterated-product-Concrete-Group Y))
              ( λ where refl → is-set-type-iterated-product-Concrete-Group))

  classifying-1-type-iterated-product-Concrete-Group : Truncated-Type l one-𝕋
  classifying-1-type-iterated-product-Concrete-Group =
    pair
      classifying-type-iterated-product-Concrete-Group
      is-1-type-classifying-type-iterated-product-Concrete-Group

  Id-iterated-product-BG-Set :
    (X Y : classifying-type-iterated-product-Concrete-Group) → Set l
  Id-iterated-product-BG-Set X Y =
    Id-Set classifying-1-type-iterated-product-Concrete-Group X Y

  unit-iterated-product-Concrete-Group : type-iterated-product-Concrete-Group
  unit-iterated-product-Concrete-Group =
    unit-∞-Group ∞-group-iterated-product-Concrete-Group

  mul-iterated-product-Concrete-Group :
    (x y : type-iterated-product-Concrete-Group) →
    type-iterated-product-Concrete-Group
  mul-iterated-product-Concrete-Group =
    mul-∞-Group ∞-group-iterated-product-Concrete-Group

  mul-iterated-product-Concrete-Group' :
    (x y : type-iterated-product-Concrete-Group) →
    type-iterated-product-Concrete-Group
  mul-iterated-product-Concrete-Group' x y =
    mul-iterated-product-Concrete-Group y x

  associative-mul-iterated-product-Concrete-Group :
    (x y z : type-iterated-product-Concrete-Group) →
    Id
      ( mul-iterated-product-Concrete-Group
        ( mul-iterated-product-Concrete-Group x y)
        ( z))
      ( mul-iterated-product-Concrete-Group
        ( x)
        ( mul-iterated-product-Concrete-Group y z))
  associative-mul-iterated-product-Concrete-Group =
    associative-mul-∞-Group ∞-group-iterated-product-Concrete-Group

  left-unit-law-mul-iterated-product-Concrete-Group :
    (x : type-iterated-product-Concrete-Group) →
    Id
      ( mul-iterated-product-Concrete-Group
        ( unit-iterated-product-Concrete-Group)
        ( x))
      ( x)
  left-unit-law-mul-iterated-product-Concrete-Group =
    left-unit-law-mul-∞-Group ∞-group-iterated-product-Concrete-Group

  right-unit-law-mul-iterated-product-Concrete-Group :
    (y : type-iterated-product-Concrete-Group) →
    Id
      ( mul-iterated-product-Concrete-Group
        ( y)
        ( unit-iterated-product-Concrete-Group))
      ( y)
  right-unit-law-mul-iterated-product-Concrete-Group =
    right-unit-law-mul-∞-Group ∞-group-iterated-product-Concrete-Group

  coherence-unit-laws-mul-iterated-product-Concrete-Group :
    Id
      ( left-unit-law-mul-iterated-product-Concrete-Group
          unit-iterated-product-Concrete-Group)
      ( right-unit-law-mul-iterated-product-Concrete-Group
          unit-iterated-product-Concrete-Group)
  coherence-unit-laws-mul-iterated-product-Concrete-Group =
    coherence-unit-laws-mul-∞-Group ∞-group-iterated-product-Concrete-Group

  inv-iterated-product-Concrete-Group :
    type-iterated-product-Concrete-Group → type-iterated-product-Concrete-Group
  inv-iterated-product-Concrete-Group =
    inv-∞-Group ∞-group-iterated-product-Concrete-Group

  left-inverse-law-mul-iterated-product-Concrete-Group :
    (x : type-iterated-product-Concrete-Group) →
    Id
      ( mul-iterated-product-Concrete-Group
        ( inv-iterated-product-Concrete-Group x)
        ( x))
      ( unit-iterated-product-Concrete-Group)
  left-inverse-law-mul-iterated-product-Concrete-Group =
    left-inverse-law-mul-∞-Group ∞-group-iterated-product-Concrete-Group

  right-inverse-law-mul-iterated-product-Concrete-Group :
    (x : type-iterated-product-Concrete-Group) →
    Id
      ( mul-iterated-product-Concrete-Group
        ( x)
        ( inv-iterated-product-Concrete-Group x))
      ( unit-iterated-product-Concrete-Group)
  right-inverse-law-mul-iterated-product-Concrete-Group =
    right-inverse-law-mul-∞-Group ∞-group-iterated-product-Concrete-Group

  group-iterated-product-Concrete-Group : Group l
  pr1 (pr1 group-iterated-product-Concrete-Group) =
    set-iterated-product-Concrete-Group
  pr1 (pr2 (pr1 group-iterated-product-Concrete-Group)) =
    mul-iterated-product-Concrete-Group
  pr2 (pr2 (pr1 group-iterated-product-Concrete-Group)) =
    associative-mul-iterated-product-Concrete-Group
  pr1 (pr1 (pr2 group-iterated-product-Concrete-Group)) =
    unit-iterated-product-Concrete-Group
  pr1 (pr2 (pr1 (pr2 group-iterated-product-Concrete-Group))) =
    left-unit-law-mul-iterated-product-Concrete-Group
  pr2 (pr2 (pr1 (pr2 group-iterated-product-Concrete-Group))) =
    right-unit-law-mul-iterated-product-Concrete-Group
  pr1 (pr2 (pr2 group-iterated-product-Concrete-Group)) =
    inv-iterated-product-Concrete-Group
  pr1 (pr2 (pr2 (pr2 group-iterated-product-Concrete-Group))) =
    left-inverse-law-mul-iterated-product-Concrete-Group
  pr2 (pr2 (pr2 (pr2 group-iterated-product-Concrete-Group))) =
    right-inverse-law-mul-iterated-product-Concrete-Group

  op-group-iterated-product-Concrete-Group : Group l
  pr1 (pr1 op-group-iterated-product-Concrete-Group) =
    set-iterated-product-Concrete-Group
  pr1 (pr2 (pr1 op-group-iterated-product-Concrete-Group)) =
    mul-iterated-product-Concrete-Group'
  pr2 (pr2 (pr1 op-group-iterated-product-Concrete-Group)) x y z =
    inv (associative-mul-iterated-product-Concrete-Group z y x)
  pr1 (pr1 (pr2 op-group-iterated-product-Concrete-Group)) =
    unit-iterated-product-Concrete-Group
  pr1 (pr2 (pr1 (pr2 op-group-iterated-product-Concrete-Group))) =
    right-unit-law-mul-iterated-product-Concrete-Group
  pr2 (pr2 (pr1 (pr2 op-group-iterated-product-Concrete-Group))) =
    left-unit-law-mul-iterated-product-Concrete-Group
  pr1 (pr2 (pr2 op-group-iterated-product-Concrete-Group)) =
    inv-iterated-product-Concrete-Group
  pr1 (pr2 (pr2 (pr2 op-group-iterated-product-Concrete-Group))) =
    right-inverse-law-mul-iterated-product-Concrete-Group
  pr2 (pr2 (pr2 (pr2 op-group-iterated-product-Concrete-Group))) =
    left-inverse-law-mul-iterated-product-Concrete-Group
```

## Properties

```agda
equiv-type-Concrete-group-iterated-product-Concrete-Group :
  {l : Level} (n : ℕ) (G : Fin n → Concrete-Group l) →
  ( type-iterated-product-Concrete-Group n G) ≃
  ( iterated-product-Fin-recursive n (type-Concrete-Group ∘ G))
equiv-type-Concrete-group-iterated-product-Concrete-Group zero-ℕ G =
  equiv-is-contr
    ( is-proof-irrelevant-is-prop
        ( is-set-is-contr is-contr-raise-unit raise-star raise-star) refl)
    is-contr-raise-unit
equiv-type-Concrete-group-iterated-product-Concrete-Group (succ-ℕ n) G =
  equiv-product
    ( id-equiv)
    ( equiv-type-Concrete-group-iterated-product-Concrete-Group n (G ∘ inl)) ∘e
  equiv-type-Concrete-Group-product-Concrete-Group
    ( G (inr star))
    ( iterated-product-Concrete-Group n (G ∘ inl))
```
