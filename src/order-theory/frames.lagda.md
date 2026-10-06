# Frames

```agda
module order-theory.frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.meet-suplattices
open import order-theory.posets
open import order-theory.suplattices
```

</details>

## Idea

A **frame** is a [meet-suplattice](order-theory.meet-suplattices.md) with
arbitrary joins in which meets distribute over suprema. The **distributive law
for meets over suprema** states that in any
[meet-suplattice](order-theory.meet-suplattices.md) `A`, we have

```text
  x ∧ (⋁ᵢ yᵢ) ＝ ⋁ᵢ (x ∧ yᵢ)
```

for every element `x : A` and any family `y : I → A`.

## Definitions

### Statement of (instances of) the infinite distributive law

#### In posets

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2)
  where

  module _
    {I : UU l3} {x : type-Poset P} {y : I → type-Poset P}
    (H : has-least-upper-bound-family-of-elements-Poset P y)
    (K : has-greatest-binary-lower-bound-Poset P x (pr1 H))
    (L : (i : I) → has-greatest-binary-lower-bound-Poset P x (y i))
    (M : has-least-upper-bound-family-of-elements-Poset P (λ i → (pr1 (L i))))
    where

    instance-distributive-law-meet-sup-Poset-Prop : Prop l1
    instance-distributive-law-meet-sup-Poset-Prop =
      Id-Prop (set-Poset P) (pr1 K) (pr1 M)

    instance-distributive-law-meet-sup-Poset : UU l1
    instance-distributive-law-meet-sup-Poset =
      type-Prop instance-distributive-law-meet-sup-Poset-Prop

    is-prop-instance-distributive-law-meet-sup-Poset :
      is-prop instance-distributive-law-meet-sup-Poset
    is-prop-instance-distributive-law-meet-sup-Poset =
      is-prop-type-Prop instance-distributive-law-meet-sup-Poset-Prop

  module _
    ( H : is-meet-semilattice-Poset P)
    ( K : is-suplattice-Poset l3 P)
    where

    distributive-law-meet-sup-Poset-Prop : Prop (l1 ⊔ lsuc l3)
    distributive-law-meet-sup-Poset-Prop =
      Π-Prop
        ( type-Poset P)
        ( λ x →
          implicit-Π-Prop
            ( UU l3)
            ( λ I →
              Π-Prop
                ( I → type-Poset P)
                ( λ y →
                  instance-distributive-law-meet-sup-Poset-Prop {I} {x} {y}
                    ( K I y)
                    ( H x (pr1 (K I y)))
                    ( λ i → H x (y i))
                    ( K I (λ i → pr1 (H x (y i)))))))

    distributive-law-meet-sup-Poset : UU (l1 ⊔ lsuc l3)
    distributive-law-meet-sup-Poset =
      type-Prop distributive-law-meet-sup-Poset-Prop

    is-prop-distributive-law-meet-sup-Poset :
      is-prop distributive-law-meet-sup-Poset
    is-prop-distributive-law-meet-sup-Poset =
      is-prop-type-Prop distributive-law-meet-sup-Poset-Prop
```

#### In meet-semilattices

```agda
instance-distributive-law-meet-sup-Meet-Semilattice :
  {l1 l2 : Level} (L : Meet-Semilattice l1) {I : UU l2}
  ( x : type-Meet-Semilattice L)
  { y : I → type-Meet-Semilattice L} →
  ( H :
    has-least-upper-bound-family-of-elements-Poset
      ( poset-Meet-Semilattice L)
      ( y))
  ( K :
    has-least-upper-bound-family-of-elements-Poset
      ( poset-Meet-Semilattice L)
      ( λ i → meet-Meet-Semilattice L x (y i))) →
  UU l1
instance-distributive-law-meet-sup-Meet-Semilattice L x {y} H =
  instance-distributive-law-meet-sup-Poset
    ( poset-Meet-Semilattice L)
    ( H)
    ( has-greatest-binary-lower-bound-Meet-Semilattice L x (pr1 H))
    ( λ i → has-greatest-binary-lower-bound-Meet-Semilattice L x (y i))
```

#### Statement of the distributive law in meet-suplattices

```agda
module _
  {l1 l2 : Level} (L : Meet-Suplattice l1 l2)
  where

  private
    _∧_ = meet-Meet-Suplattice L
    ⋁_ = sup-Meet-Suplattice L

  distributive-law-Meet-Suplattice-Prop : Prop (l1 ⊔ lsuc l2)
  distributive-law-Meet-Suplattice-Prop =
    Π-Prop
      ( type-Meet-Suplattice L)
      ( λ x →
        implicit-Π-Prop
          ( UU l2)
          ( λ I →
            Π-Prop
              ( I → type-Meet-Suplattice L)
              ( λ y →
                Id-Prop
                  ( set-Meet-Suplattice L)
                  ( x ∧ (⋁ y))
                  ( ⋁ (λ i → (x ∧ (y i)))))))

  distributive-law-Meet-Suplattice : UU (l1 ⊔ lsuc l2)
  distributive-law-Meet-Suplattice =
    type-Prop distributive-law-Meet-Suplattice-Prop

  is-prop-distributive-law-Meet-Suplattice :
    is-prop distributive-law-Meet-Suplattice
  is-prop-distributive-law-Meet-Suplattice =
    is-prop-type-Prop distributive-law-Meet-Suplattice-Prop
```

### The predicate on meet-suplattices to be a frame

```agda
module _
  {l1 l2 : Level} (L : Meet-Suplattice l1 l2)
  where

  is-frame-Meet-Suplattice-Prop : Prop (l1 ⊔ lsuc l2)
  is-frame-Meet-Suplattice-Prop = distributive-law-Meet-Suplattice-Prop L

  is-frame-Meet-Suplattice : UU (l1 ⊔ lsuc l2)
  is-frame-Meet-Suplattice = type-Prop is-frame-Meet-Suplattice-Prop

  is-prop-is-frame-Meet-Suplattice : is-prop is-frame-Meet-Suplattice
  is-prop-is-frame-Meet-Suplattice =
    is-prop-type-Prop is-frame-Meet-Suplattice-Prop
```

### Frames

```agda
Frame : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Frame l1 l2 = Σ (Meet-Suplattice l1 l2) is-frame-Meet-Suplattice

module _
  {l1 l2 : Level} (A : Frame l1 l2)
  where

  meet-suplattice-Frame : Meet-Suplattice l1 l2
  meet-suplattice-Frame = pr1 A

  meet-semilattice-Frame : Meet-Semilattice l1
  meet-semilattice-Frame =
    meet-semilattice-Meet-Suplattice meet-suplattice-Frame

  suplattice-Frame : Suplattice l1 l1 l2
  suplattice-Frame = suplattice-Meet-Suplattice meet-suplattice-Frame

  poset-Frame : Poset l1 l1
  poset-Frame = poset-Meet-Suplattice meet-suplattice-Frame

  set-Frame : Set l1
  set-Frame = set-Poset poset-Frame

  type-Frame : UU l1
  type-Frame = type-Poset poset-Frame

  is-set-type-Frame : is-set type-Frame
  is-set-type-Frame = is-set-type-Poset poset-Frame

  leq-Frame-Prop : (x y : type-Frame) → Prop l1
  leq-Frame-Prop = leq-prop-Poset poset-Frame

  leq-Frame : (x y : type-Frame) → UU l1
  leq-Frame = leq-Poset poset-Frame

  is-prop-leq-Frame : (x y : type-Frame) → is-prop (leq-Frame x y)
  is-prop-leq-Frame = is-prop-leq-Poset poset-Frame

  refl-leq-Frame : is-reflexive leq-Frame
  refl-leq-Frame = refl-leq-Poset poset-Frame

  antisymmetric-leq-Frame : is-antisymmetric leq-Frame
  antisymmetric-leq-Frame = antisymmetric-leq-Poset poset-Frame

  transitive-leq-Frame : is-transitive leq-Frame
  transitive-leq-Frame = transitive-leq-Poset poset-Frame

  meet-Frame : type-Frame → type-Frame → type-Frame
  meet-Frame = meet-Meet-Semilattice meet-semilattice-Frame

  is-greatest-binary-lower-bound-meet-Frame :
    (x y : type-Frame) →
    is-greatest-binary-lower-bound-Poset poset-Frame x y (meet-Frame x y)
  is-greatest-binary-lower-bound-meet-Frame =
    is-greatest-binary-lower-bound-meet-Meet-Semilattice meet-semilattice-Frame

  associative-meet-Frame :
    (x y z : type-Frame) →
    meet-Frame (meet-Frame x y) z ＝ meet-Frame x (meet-Frame y z)
  associative-meet-Frame =
    associative-meet-Meet-Semilattice meet-semilattice-Frame

  commutative-meet-Frame :
    (x y : type-Frame) → meet-Frame x y ＝ meet-Frame y x
  commutative-meet-Frame =
    commutative-meet-Meet-Semilattice meet-semilattice-Frame

  idempotent-meet-Frame :
    (x : type-Frame) → meet-Frame x x ＝ x
  idempotent-meet-Frame =
    idempotent-meet-Meet-Semilattice meet-semilattice-Frame

  is-suplattice-Frame :
    is-suplattice-Poset l2 poset-Frame
  is-suplattice-Frame = is-suplattice-Suplattice suplattice-Frame

  sup-Frame : {I : UU l2} → (I → type-Frame) → type-Frame
  sup-Frame = sup-Suplattice suplattice-Frame

  is-least-upper-bound-sup-Frame :
    {I : UU l2} (x : I → type-Frame) →
    is-least-upper-bound-family-of-elements-Poset poset-Frame x (sup-Frame x)
  is-least-upper-bound-sup-Frame =
    is-least-upper-bound-sup-Suplattice suplattice-Frame

  distributive-meet-sup-Frame :
    distributive-law-Meet-Suplattice meet-suplattice-Frame
  distributive-meet-sup-Frame = pr2 A
```
