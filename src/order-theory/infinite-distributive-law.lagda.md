# Infinite distributive law

```agda
module order-theory.infinite-distributive-law where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
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

The **distributive law for meets over suprema** states that in any
[meet-suplattice](order-theory.meet-suplattices.md) `A`, we have

```md
  x ∧ (⋁ᵢ yᵢ) ＝ ⋁ᵢ (x ∧ yᵢ)
```

for every element `x : A` and any family `y : I → A`.

## Definition

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
          Π-Prop'
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
        Π-Prop'
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
