# Nuclei on large locales

```agda
module order-theory.nuclei-large-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.homomorphisms-large-meet-semilattices
open import order-theory.large-frames
open import order-theory.large-locales
open import order-theory.large-meet-semilattices
open import order-theory.large-meet-subsemilattices
open import order-theory.large-posets
open import order-theory.large-subposets
open import order-theory.large-subpreorders
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
```

</details>

## Idea

A **nucleus** on a [large locale](order-theory.large-locales.md) `L` is an order
preserving map `j : hom-Large-Poset id L L` such that `j` preserves meets and is
inflationary and idempotent.

## Definitions

### Nuclei on large locales

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Locale α β γ)
  where

  record
    nucleus-Large-Locale : UUω
    where
    field
      hom-large-meet-semilattice-nucleus-Large-Locale :
        hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Locale L)
          ( large-meet-semilattice-Large-Locale L)
      is-inflationary-nucleus-Large-Locale :
        {l1 : Level} (x : type-Large-Locale L l1) →
        leq-Large-Locale L x
          ( map-hom-Large-Meet-Semilattice
            ( large-meet-semilattice-Large-Locale L)
            ( large-meet-semilattice-Large-Locale L)
            ( hom-large-meet-semilattice-nucleus-Large-Locale)
            ( x))
      is-idempotent-nucleus-Large-Locale :
        {l1 : Level} (x : type-Large-Locale L l1) →
        map-hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Locale L)
          ( large-meet-semilattice-Large-Locale L)
          ( hom-large-meet-semilattice-nucleus-Large-Locale)
          ( map-hom-Large-Meet-Semilattice
            ( large-meet-semilattice-Large-Locale L)
            ( large-meet-semilattice-Large-Locale L)
            ( hom-large-meet-semilattice-nucleus-Large-Locale)
            ( x)) ＝
        map-hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Locale L)
          ( large-meet-semilattice-Large-Locale L)
          ( hom-large-meet-semilattice-nucleus-Large-Locale)
          ( x)

  open nucleus-Large-Locale public

  module _
    (j : nucleus-Large-Locale)
    where

    map-nucleus-Large-Locale :
      {l1 : Level} → type-Large-Locale L l1 → type-Large-Locale L l1
    map-nucleus-Large-Locale =
      map-hom-Large-Meet-Semilattice
        ( large-meet-semilattice-Large-Locale L)
        ( large-meet-semilattice-Large-Locale L)
        ( hom-large-meet-semilattice-nucleus-Large-Locale j)

    preserves-order-nucleus-Large-Locale :
      {l1 l2 : Level}
      (x : type-Large-Locale L l1)
      (y : type-Large-Locale L l2) →
      leq-Large-Locale L x y →
      leq-Large-Locale L
        ( map-nucleus-Large-Locale x)
        ( map-nucleus-Large-Locale y)
    preserves-order-nucleus-Large-Locale =
      preserves-order-hom-Large-Meet-Semilattice
        ( large-meet-semilattice-Large-Locale L)
        ( large-meet-semilattice-Large-Locale L)
        ( hom-large-meet-semilattice-nucleus-Large-Locale j)

    preserves-meets-nucleus-Large-Locale :
      {l1 l2 : Level}
      (x : type-Large-Locale L l1)
      (y : type-Large-Locale L l2) →
      map-nucleus-Large-Locale (meet-Large-Locale L x y) ＝
      meet-Large-Locale L
        ( map-nucleus-Large-Locale x)
        ( map-nucleus-Large-Locale y)
    preserves-meets-nucleus-Large-Locale =
      preserves-meets-hom-Large-Meet-Semilattice
        ( hom-large-meet-semilattice-nucleus-Large-Locale j)

    preserves-top-nucleus-Large-Locale :
      map-nucleus-Large-Locale (top-Large-Locale L) ＝ top-Large-Locale L
    preserves-top-nucleus-Large-Locale =
      preserves-top-hom-Large-Meet-Semilattice
        ( hom-large-meet-semilattice-nucleus-Large-Locale j)
```

### The large locale of `j`-closed elements of a nucleus

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Locale α β γ) (j : nucleus-Large-Locale L)
  where

  large-subpreorder-nucleus-Large-Locale :
    Large-Subpreorder α (large-preorder-Large-Locale L)
  large-subpreorder-nucleus-Large-Locale {l1} x =
    Id-Prop (set-Large-Locale L l1) (map-nucleus-Large-Locale L j x) x

  is-closed-element-nucleus-Large-Locale :
    {l1 : Level} → type-Large-Locale L l1 → UU (α l1)
  is-closed-element-nucleus-Large-Locale =
    is-in-Large-Subpreorder
      ( large-preorder-Large-Locale L)
      ( large-subpreorder-nucleus-Large-Locale)

  is-prop-is-closed-element-nucleus-Large-Locale :
    {l1 : Level} (x : type-Large-Locale L l1) →
    is-prop (is-closed-element-nucleus-Large-Locale x)
  is-prop-is-closed-element-nucleus-Large-Locale =
    is-prop-is-in-Large-Subpreorder
      ( large-preorder-Large-Locale L)
      ( large-subpreorder-nucleus-Large-Locale)

  is-closed-element-leq-nucleus-Large-Locale :
    {l1 : Level} (x : type-Large-Locale L l1) →
    leq-Large-Locale L (map-nucleus-Large-Locale L j x) x →
    is-closed-element-nucleus-Large-Locale x
  is-closed-element-leq-nucleus-Large-Locale x H =
    antisymmetric-leq-Large-Locale L
      ( map-nucleus-Large-Locale L j x)
      ( x)
      ( H)
      (is-inflationary-nucleus-Large-Locale j x)

  closed-element-nucleus-Large-Locale :
    (l1 : Level) → UU (α l1)
  closed-element-nucleus-Large-Locale =
    type-Large-Subpreorder
      ( large-preorder-Large-Locale L)
      ( large-subpreorder-nucleus-Large-Locale)

  is-closed-under-sim-nucleus-Large-Locale :
    {l1 l2 : Level}
    (x : type-Large-Locale L l1)
    (y : type-Large-Locale L l2) →
    leq-Large-Locale L x y → leq-Large-Locale L y x →
    is-closed-element-nucleus-Large-Locale x →
    is-closed-element-nucleus-Large-Locale y
  is-closed-under-sim-nucleus-Large-Locale x y H K c =
    is-closed-element-leq-nucleus-Large-Locale y
      ( transitive-leq-Large-Locale L
        ( map-nucleus-Large-Locale L j y)
        ( map-nucleus-Large-Locale L j x)
        ( y)
        ( transitive-leq-Large-Locale L
          ( map-nucleus-Large-Locale L j x)
          ( x)
          ( y)
          ( H)
          ( leq-eq-Large-Locale L c))
        ( preserves-order-nucleus-Large-Locale L j y x K))

  large-subposet-nucleus-Large-Locale :
    Large-Subposet α (large-poset-Large-Locale L)
  large-subpreorder-Large-Subposet
    large-subposet-nucleus-Large-Locale =
    large-subpreorder-nucleus-Large-Locale
  is-closed-under-sim-Large-Subposet
    large-subposet-nucleus-Large-Locale =
    is-closed-under-sim-nucleus-Large-Locale

  large-poset-nucleus-Large-Locale :
    Large-Poset α β
  large-poset-nucleus-Large-Locale =
    large-poset-Large-Subposet
      ( large-poset-Large-Locale L)
      ( large-subposet-nucleus-Large-Locale)

  leq-closed-element-nucleus-Large-Locale-Prop :
    Large-Relation-Prop α β closed-element-nucleus-Large-Locale
  leq-closed-element-nucleus-Large-Locale-Prop =
    leq-Large-Subposet-Prop
      ( large-poset-Large-Locale L)
      ( large-subposet-nucleus-Large-Locale)

  leq-closed-element-nucleus-Large-Locale :
    Large-Relation α β closed-element-nucleus-Large-Locale
  leq-closed-element-nucleus-Large-Locale =
    leq-Large-Subposet
      ( large-poset-Large-Locale L)
      ( large-subposet-nucleus-Large-Locale)

  is-prop-leq-closed-element-nucleus-Large-Locale :
    is-prop-Large-Relation
      ( closed-element-nucleus-Large-Locale)
      ( leq-closed-element-nucleus-Large-Locale)
  is-prop-leq-closed-element-nucleus-Large-Locale =
    is-prop-leq-Large-Subposet
      ( large-poset-Large-Locale L)
      ( large-subposet-nucleus-Large-Locale)

  refl-leq-closed-element-nucleus-Large-Locale :
    is-large-reflexive
      ( closed-element-nucleus-Large-Locale)
      ( leq-closed-element-nucleus-Large-Locale)
  refl-leq-closed-element-nucleus-Large-Locale =
    refl-leq-Large-Subposet
      ( large-poset-Large-Locale L)
      ( large-subposet-nucleus-Large-Locale)

  antisymmetric-leq-closed-element-nucleus-Large-Locale :
    is-large-antisymmetric
      ( closed-element-nucleus-Large-Locale)
      ( leq-closed-element-nucleus-Large-Locale)
  antisymmetric-leq-closed-element-nucleus-Large-Locale =
    antisymmetric-leq-Large-Subposet
      ( large-poset-Large-Locale L)
      ( large-subposet-nucleus-Large-Locale)

  transitive-leq-closed-element-nucleus-Large-Locale :
    is-large-transitive
      ( closed-element-nucleus-Large-Locale)
      ( leq-closed-element-nucleus-Large-Locale)
  transitive-leq-closed-element-nucleus-Large-Locale =
    transitive-leq-Large-Subposet
      ( large-poset-Large-Locale L)
      ( large-subposet-nucleus-Large-Locale)

  is-closed-under-meets-large-subposet-nucleus-Large-Locale :
    is-closed-under-meets-Large-Subposet
      ( large-meet-semilattice-Large-Locale L)
      ( large-subposet-nucleus-Large-Locale)
  is-closed-under-meets-large-subposet-nucleus-Large-Locale x y p q =
    ( preserves-meets-nucleus-Large-Locale L j x y) ∙
    ( ap-meet-Large-Locale L p q)

  contains-top-large-subposet-nucleus-Large-Locale :
    contains-top-Large-Subposet
      ( large-meet-semilattice-Large-Locale L)
      ( large-subposet-nucleus-Large-Locale)
  contains-top-large-subposet-nucleus-Large-Locale =
    is-closed-element-leq-nucleus-Large-Locale
      ( top-Large-Locale L)
      ( is-top-element-top-Large-Locale L
        ( map-nucleus-Large-Locale L j (top-Large-Locale L)))

  large-meet-subsemilattice-nucleus-Large-Locale :
    Large-Meet-Subsemilattice α (large-meet-semilattice-Large-Locale L)
  large-subposet-Large-Meet-Subsemilattice
    large-meet-subsemilattice-nucleus-Large-Locale =
    large-subposet-nucleus-Large-Locale
  is-closed-under-meets-Large-Meet-Subsemilattice
    large-meet-subsemilattice-nucleus-Large-Locale =
    is-closed-under-meets-large-subposet-nucleus-Large-Locale
  contains-top-Large-Meet-Subsemilattice
    large-meet-subsemilattice-nucleus-Large-Locale =
    contains-top-large-subposet-nucleus-Large-Locale

  is-large-meet-semilattice-nucleus-Large-Locale :
    is-large-meet-semilattice-Large-Poset
      ( large-poset-nucleus-Large-Locale)
  is-large-meet-semilattice-nucleus-Large-Locale =
    is-large-meet-semilattice-Large-Meet-Subsemilattice
      ( large-meet-semilattice-Large-Locale L)
      ( large-meet-subsemilattice-nucleus-Large-Locale)

  large-meet-semilattice-nucleus-Large-Locale :
    Large-Meet-Semilattice α β
  large-meet-semilattice-nucleus-Large-Locale =
    large-meet-semilattice-Large-Meet-Subsemilattice
      ( large-meet-semilattice-Large-Locale L)
      ( large-meet-subsemilattice-nucleus-Large-Locale)

  meet-closed-element-nucleus-Large-Locale :
    {l1 l2 : Level} →
    closed-element-nucleus-Large-Locale l1 →
    closed-element-nucleus-Large-Locale l2 →
    closed-element-nucleus-Large-Locale (l1 ⊔ l2)
  meet-closed-element-nucleus-Large-Locale =
    meet-Large-Meet-Semilattice large-meet-semilattice-nucleus-Large-Locale

  forward-implication-adjoint-relation-nucleus-Large-Locale :
    {l1 l2 : Level}
    {x : type-Large-Locale L l1}
    {y : type-Large-Locale L l2} →
    is-closed-element-nucleus-Large-Locale y →
    leq-Large-Locale L x y →
    leq-Large-Locale L (map-nucleus-Large-Locale L j x) y
  forward-implication-adjoint-relation-nucleus-Large-Locale {x = x} {y} H K =
    transitive-leq-Large-Locale L
      ( map-nucleus-Large-Locale L j x)
      ( map-nucleus-Large-Locale L j y)
      ( y)
      ( leq-eq-Large-Locale L H)
      ( preserves-order-nucleus-Large-Locale L j
        ( x)
        ( y)
        ( K))

  backward-implication-adjoint-relation-nucleus-Large-Locale :
    {l1 l2 : Level}
    {x : type-Large-Locale L l1}
    {y : type-Large-Locale L l2} →
    leq-Large-Locale L (map-nucleus-Large-Locale L j x) y →
    leq-Large-Locale L x y
  backward-implication-adjoint-relation-nucleus-Large-Locale {x = x} {y} H =
    transitive-leq-Large-Locale L
      ( x)
      ( map-nucleus-Large-Locale L j x)
      ( y)
      ( H)
      ( is-inflationary-nucleus-Large-Locale j x)

  adjoint-relation-nucleus-Large-Locale :
    {l1 l2 : Level}
    (x : type-Large-Locale L l1)
    (y : type-Large-Locale L l2) →
    is-closed-element-nucleus-Large-Locale y →
    leq-Large-Locale L x y ↔
    leq-Large-Locale L (map-nucleus-Large-Locale L j x) y
  pr1 (adjoint-relation-nucleus-Large-Locale x y H) =
    forward-implication-adjoint-relation-nucleus-Large-Locale H
  pr2 (adjoint-relation-nucleus-Large-Locale x y H) =
    backward-implication-adjoint-relation-nucleus-Large-Locale

  sup-closed-element-nucleus-Large-Locale :
    {l1 l2 : Level} {I : UU l1}
    (x : I → closed-element-nucleus-Large-Locale l2) →
    closed-element-nucleus-Large-Locale (γ ⊔ l1 ⊔ l2)
  pr1 (sup-closed-element-nucleus-Large-Locale x) =
    map-nucleus-Large-Locale L j (sup-Large-Locale L (pr1 ∘ x))
  pr2 (sup-closed-element-nucleus-Large-Locale x) =
    is-idempotent-nucleus-Large-Locale j (sup-Large-Locale L (pr1 ∘ x))

  is-least-upper-bound-sup-closed-element-nucleus-Large-Locale :
    {l1 l2 : Level} {I : UU l1}
    (x : I → closed-element-nucleus-Large-Locale l2) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-nucleus-Large-Locale)
      ( x)
      ( sup-closed-element-nucleus-Large-Locale x)
  pr1 (is-least-upper-bound-sup-closed-element-nucleus-Large-Locale x y) H =
    forward-implication-adjoint-relation-nucleus-Large-Locale
      ( pr2 y)
      ( forward-implication
        ( is-least-upper-bound-sup-Large-Locale L (pr1 ∘ x) (pr1 y))
        ( H))
  pr2 (is-least-upper-bound-sup-closed-element-nucleus-Large-Locale x y) H =
    backward-implication
      ( is-least-upper-bound-sup-Large-Locale L (pr1 ∘ x) (pr1 y))
      ( backward-implication-adjoint-relation-nucleus-Large-Locale H)

  is-large-suplattice-large-poset-nucleus-Large-Locale :
    is-large-suplattice-Large-Poset γ
      ( large-poset-nucleus-Large-Locale)
  sup-has-least-upper-bound-family-of-elements-Large-Poset
    ( is-large-suplattice-large-poset-nucleus-Large-Locale x) =
    sup-closed-element-nucleus-Large-Locale x
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset
    ( is-large-suplattice-large-poset-nucleus-Large-Locale x) =
    is-least-upper-bound-sup-closed-element-nucleus-Large-Locale x

  large-suplattice-nucleus-Large-Locale :
    Large-Suplattice α β γ
  large-poset-Large-Suplattice
    large-suplattice-nucleus-Large-Locale =
    large-poset-nucleus-Large-Locale
  is-large-suplattice-Large-Suplattice
    large-suplattice-nucleus-Large-Locale =
    is-large-suplattice-large-poset-nucleus-Large-Locale

  distributive-meet-sup-nucleus-Large-Locale :
    {l1 l2 l3 : Level}
    (x : closed-element-nucleus-Large-Locale l1)
    {I : UU l2} (y : I → closed-element-nucleus-Large-Locale l3) →
    meet-closed-element-nucleus-Large-Locale x
      ( sup-closed-element-nucleus-Large-Locale y) ＝
    sup-closed-element-nucleus-Large-Locale
      ( λ i →
        meet-closed-element-nucleus-Large-Locale x (y i))
  distributive-meet-sup-nucleus-Large-Locale (x , p) y =
    eq-type-subtype
      ( large-subpreorder-nucleus-Large-Locale)
      ( ( ap (λ u → meet-Large-Locale L u _) (inv p)) ∙
        ( ( inv ( preserves-meets-nucleus-Large-Locale L j x _)) ∙
          ( ap
            ( map-nucleus-Large-Locale L j)
            ( distributive-meet-sup-Large-Locale L x (pr1 ∘ y)))))

  large-frame-nucleus-Large-Locale :
    Large-Frame α β γ
  large-poset-Large-Frame
    large-frame-nucleus-Large-Locale =
    large-poset-nucleus-Large-Locale
  is-large-meet-semilattice-Large-Frame
    large-frame-nucleus-Large-Locale =
    is-large-meet-semilattice-nucleus-Large-Locale
  is-large-suplattice-Large-Frame
    large-frame-nucleus-Large-Locale =
    is-large-suplattice-large-poset-nucleus-Large-Locale
  distributive-meet-sup-Large-Frame
    large-frame-nucleus-Large-Locale =
    distributive-meet-sup-nucleus-Large-Locale

  large-locale-nucleus-Large-Locale :
    Large-Locale α β γ
  large-locale-nucleus-Large-Locale = large-frame-nucleus-Large-Locale
```
