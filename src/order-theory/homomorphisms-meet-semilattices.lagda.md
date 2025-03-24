# Homomorphisms of meet-semilattices

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.homomorphisms-meet-semilattices
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups funext univalence truncations

open import order-theory.greatest-lower-bounds-posets funext univalence truncations
open import order-theory.meet-semilattices funext univalence truncations
open import order-theory.order-preserving-maps-posets funext univalence truncations
```

</details>

## Idea

A **homomorphism of meet-semilattice** is a map that preserves meets. It follows
that homomorphisms of meet-semilattices are order preserving.

## Definitions

### Homomorphisms of algebraic meet-semilattices

```agda
module _
  {l1 l2 : Level}
  (A : Meet-Semilattice l1) (B : Meet-Semilattice l2)
  where

  preserves-meet-Prop :
    (type-Meet-Semilattice A → type-Meet-Semilattice B) → Prop (l1 ⊔ l2)
  preserves-meet-Prop =
    preserves-mul-prop-Semigroup
      ( semigroup-Meet-Semilattice A)
      ( semigroup-Meet-Semilattice B)

  preserves-meet :
    (type-Meet-Semilattice A → type-Meet-Semilattice B) → UU (l1 ⊔ l2)
  preserves-meet =
    preserves-mul-Semigroup
      ( semigroup-Meet-Semilattice A)
      ( semigroup-Meet-Semilattice B)

  is-prop-preserves-meet :
    (f : type-Meet-Semilattice A → type-Meet-Semilattice B) →
    is-prop (preserves-meet f)
  is-prop-preserves-meet =
    is-prop-preserves-mul-Semigroup
      ( semigroup-Meet-Semilattice A)
      ( semigroup-Meet-Semilattice B)

  hom-set-Meet-Semilattice : Set (l1 ⊔ l2)
  hom-set-Meet-Semilattice =
    hom-set-Semigroup
      ( semigroup-Meet-Semilattice A)
      ( semigroup-Meet-Semilattice B)

  hom-Meet-Semilattice : UU (l1 ⊔ l2)
  hom-Meet-Semilattice = type-Set hom-set-Meet-Semilattice

  is-set-hom-Meet-Semilattice : is-set hom-Meet-Semilattice
  is-set-hom-Meet-Semilattice = is-set-type-Set hom-set-Meet-Semilattice

  module _
    (f : hom-Meet-Semilattice)
    where

    map-hom-Meet-Semilattice :
      type-Meet-Semilattice A → type-Meet-Semilattice B
    map-hom-Meet-Semilattice = pr1 f

    preserves-meet-hom-Meet-Semilattice :
      preserves-meet map-hom-Meet-Semilattice
    preserves-meet-hom-Meet-Semilattice = pr2 f

    preserves-order-hom-Meet-Semilattice :
      preserves-order-Poset
        ( poset-Meet-Semilattice A)
        ( poset-Meet-Semilattice B)
        ( map-hom-Meet-Semilattice)
    preserves-order-hom-Meet-Semilattice x y H =
      ( inv preserves-meet-hom-Meet-Semilattice) ∙
      ( ap map-hom-Meet-Semilattice H)

    hom-poset-hom-Meet-Semilattice :
      hom-Poset (poset-Meet-Semilattice A) (poset-Meet-Semilattice B)
    pr1 hom-poset-hom-Meet-Semilattice = map-hom-Meet-Semilattice
    pr2 hom-poset-hom-Meet-Semilattice = preserves-order-hom-Meet-Semilattice
```

### Homomorphisms of order-theoretic meet-semilattices

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Order-Theoretic-Meet-Semilattice l1 l2)
  (B : Order-Theoretic-Meet-Semilattice l3 l4)
  where

  preserves-meet-hom-Poset-Prop :
    hom-Poset
      ( poset-Order-Theoretic-Meet-Semilattice A)
      ( poset-Order-Theoretic-Meet-Semilattice B) → Prop (l1 ⊔ l3 ⊔ l4)
  preserves-meet-hom-Poset-Prop (f , H) =
    Π-Prop
      ( type-Order-Theoretic-Meet-Semilattice A)
      ( λ x →
        Π-Prop
          ( type-Order-Theoretic-Meet-Semilattice A)
          ( λ y →
            is-greatest-binary-lower-bound-Poset-Prop
              ( poset-Order-Theoretic-Meet-Semilattice B)
              ( f x)
              ( f y)
              ( f (meet-Order-Theoretic-Meet-Semilattice A x y))))

  preserves-meet-hom-Poset :
    hom-Poset
      ( poset-Order-Theoretic-Meet-Semilattice A)
      ( poset-Order-Theoretic-Meet-Semilattice B) → UU (l1 ⊔ l3 ⊔ l4)
  preserves-meet-hom-Poset f =
    type-Prop (preserves-meet-hom-Poset-Prop f)

  is-prop-preserves-meet-hom-Prop :
    ( f :
      hom-Poset
        ( poset-Order-Theoretic-Meet-Semilattice A)
        ( poset-Order-Theoretic-Meet-Semilattice B)) →
    is-prop (preserves-meet-hom-Poset f)
  is-prop-preserves-meet-hom-Prop f =
    is-prop-type-Prop (preserves-meet-hom-Poset-Prop f)

  hom-set-Order-Theoretic-Meet-Semilattice : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-Order-Theoretic-Meet-Semilattice =
    set-subset
      ( hom-set-Poset
        ( poset-Order-Theoretic-Meet-Semilattice A)
        ( poset-Order-Theoretic-Meet-Semilattice B))
      ( preserves-meet-hom-Poset-Prop)
```
