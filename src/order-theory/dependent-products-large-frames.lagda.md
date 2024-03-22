# Dependent products of large frames

```agda
module order-theory.dependent-products-large-frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.sets
open import foundation.universe-levels

open import order-theory.dependent-products-large-meet-semilattices
open import order-theory.dependent-products-large-posets
open import order-theory.dependent-products-large-suplattices
open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-frames
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.top-elements-large-posets
```

</details>

Given a family `L : I → Large-Frame α β` of large frames indexed by a type
`I : UU l`, the product of the large frame `L i` is again a large frame.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  {l1 : Level} {I : UU l1} (L : I → Large-Frame α β γ)
  where

  large-poset-Π-Large-Frame :
    Large-Poset (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-poset-Π-Large-Frame =
    Π-Large-Poset (λ i → large-poset-Large-Frame (L i))

  large-meet-semilattice-Π-Large-Frame :
    Large-Meet-Semilattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-meet-semilattice-Π-Large-Frame =
    Π-Large-Meet-Semilattice (λ i → large-meet-semilattice-Large-Frame (L i))

  has-meets-Π-Large-Frame :
    has-meets-Large-Poset large-poset-Π-Large-Frame
  has-meets-Π-Large-Frame =
    has-meets-Π-Large-Poset
      ( λ i → large-poset-Large-Frame (L i))
      ( λ i → has-meets-Large-Frame (L i))

  large-suplattice-Π-Large-Frame :
    Large-Suplattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1) γ
  large-suplattice-Π-Large-Frame =
    Π-Large-Suplattice (λ i → large-suplattice-Large-Frame (L i))

  is-large-suplattice-Π-Large-Frame :
    is-large-suplattice-Large-Poset γ large-poset-Π-Large-Frame
  is-large-suplattice-Π-Large-Frame =
    is-large-suplattice-Π-Large-Suplattice
      ( λ i → large-suplattice-Large-Frame (L i))

  set-Π-Large-Frame : (l : Level) → Set (α l ⊔ l1)
  set-Π-Large-Frame = set-Large-Poset large-poset-Π-Large-Frame

  type-Π-Large-Frame : (l : Level) → UU (α l ⊔ l1)
  type-Π-Large-Frame = type-Large-Poset large-poset-Π-Large-Frame

  is-set-type-Π-Large-Frame : {l : Level} → is-set (type-Π-Large-Frame l)
  is-set-type-Π-Large-Frame =
    is-set-type-Large-Poset large-poset-Π-Large-Frame

  leq-prop-Π-Large-Frame :
    Large-Relation-Prop
      ( λ l2 l3 → β l2 l3 ⊔ l1)
      ( type-Π-Large-Frame)
  leq-prop-Π-Large-Frame =
    leq-prop-Large-Poset large-poset-Π-Large-Frame

  leq-Π-Large-Frame :
    Large-Relation
      ( λ l2 l3 → β l2 l3 ⊔ l1)
      ( type-Π-Large-Frame)
  leq-Π-Large-Frame = leq-Large-Poset large-poset-Π-Large-Frame

  is-prop-leq-Π-Large-Frame :
    is-prop-Large-Relation type-Π-Large-Frame leq-Π-Large-Frame
  is-prop-leq-Π-Large-Frame =
    is-prop-leq-Large-Poset large-poset-Π-Large-Frame

  refl-leq-Π-Large-Frame :
    is-reflexive-Large-Relation type-Π-Large-Frame leq-Π-Large-Frame
  refl-leq-Π-Large-Frame = refl-leq-Large-Poset large-poset-Π-Large-Frame

  antisymmetric-leq-Π-Large-Frame :
    is-antisymmetric-Large-Relation type-Π-Large-Frame leq-Π-Large-Frame
  antisymmetric-leq-Π-Large-Frame =
    antisymmetric-leq-Large-Poset large-poset-Π-Large-Frame

  transitive-leq-Π-Large-Frame :
    is-transitive-Large-Relation type-Π-Large-Frame leq-Π-Large-Frame
  transitive-leq-Π-Large-Frame =
    transitive-leq-Large-Poset large-poset-Π-Large-Frame

  meet-Π-Large-Frame :
    {l2 l3 : Level} →
    type-Π-Large-Frame l2 →
    type-Π-Large-Frame l3 →
    type-Π-Large-Frame (l2 ⊔ l3)
  meet-Π-Large-Frame =
    meet-has-meets-Large-Poset has-meets-Π-Large-Frame

  is-greatest-binary-lower-bound-meet-Π-Large-Frame :
    {l2 l3 : Level}
    (x : type-Π-Large-Frame l2)
    (y : type-Π-Large-Frame l3) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Π-Large-Frame)
      ( x)
      ( y)
      ( meet-Π-Large-Frame x y)
  is-greatest-binary-lower-bound-meet-Π-Large-Frame =
    is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
      has-meets-Π-Large-Frame

  top-Π-Large-Frame : type-Π-Large-Frame lzero
  top-Π-Large-Frame =
    top-Large-Meet-Semilattice large-meet-semilattice-Π-Large-Frame

  is-top-element-top-Π-Large-Frame :
    {l1 : Level} (x : type-Π-Large-Frame l1) →
    leq-Π-Large-Frame x top-Π-Large-Frame
  is-top-element-top-Π-Large-Frame =
    is-top-element-top-Large-Meet-Semilattice
      large-meet-semilattice-Π-Large-Frame

  has-top-element-Π-Large-Frame :
    has-top-element-Large-Poset large-poset-Π-Large-Frame
  has-top-element-Π-Large-Frame =
    has-top-element-Large-Meet-Semilattice
      large-meet-semilattice-Π-Large-Frame

  is-large-meet-semilattice-Π-Large-Frame :
    is-large-meet-semilattice-Large-Poset large-poset-Π-Large-Frame
  is-large-meet-semilattice-Π-Large-Frame =
    is-large-meet-semilattice-Large-Meet-Semilattice
      large-meet-semilattice-Π-Large-Frame

  sup-Π-Large-Frame :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Frame l3) →
    type-Π-Large-Frame (γ ⊔ l2 ⊔ l3)
  sup-Π-Large-Frame =
    sup-is-large-suplattice-Large-Poset γ
      ( large-poset-Π-Large-Frame)
      ( is-large-suplattice-Π-Large-Frame)

  is-least-upper-bound-sup-Π-Large-Frame :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Frame l3) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Π-Large-Frame)
      ( x)
      ( sup-Π-Large-Frame x)
  is-least-upper-bound-sup-Π-Large-Frame =
    is-least-upper-bound-sup-is-large-suplattice-Large-Poset γ
      ( large-poset-Π-Large-Frame)
      ( is-large-suplattice-Π-Large-Frame)

  distributive-meet-sup-Π-Large-Frame :
    {l2 l3 l4 : Level}
    (x : type-Π-Large-Frame l2)
    {J : UU l3} (y : J → type-Π-Large-Frame l4) →
    meet-Π-Large-Frame x (sup-Π-Large-Frame y) ＝
    sup-Π-Large-Frame (λ j → meet-Π-Large-Frame x (y j))
  distributive-meet-sup-Π-Large-Frame x y =
    eq-htpy
      ( λ i → distributive-meet-sup-Large-Frame (L i) (x i) (λ j → y j i))

  Π-Large-Frame : Large-Frame (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1) γ
  large-poset-Large-Frame Π-Large-Frame =
    large-poset-Π-Large-Frame
  is-large-meet-semilattice-Large-Frame Π-Large-Frame =
    is-large-meet-semilattice-Π-Large-Frame
  is-large-suplattice-Large-Frame Π-Large-Frame =
    is-large-suplattice-Π-Large-Frame
  distributive-meet-sup-Large-Frame Π-Large-Frame =
    distributive-meet-sup-Π-Large-Frame
```
