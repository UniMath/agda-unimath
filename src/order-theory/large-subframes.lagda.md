# Large subframes

```agda
module order-theory.large-subframes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-frames
open import order-theory.large-meet-semilattices
open import order-theory.large-meet-subsemilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-subposets
open import order-theory.large-subpreorders
open import order-theory.large-subsuplattices
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.top-elements-large-posets
```

</details>

## Idea

A **large subframe** of a [large frame](order-theory.large-frames.md) is a
[large subposet](order-theory.large-subposets.md) which is closed under meets,
contains the top element, and is closed under suprema.

## Definition

```agda
record
  Large-Subframe
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (δ : Level → Level) (F : Large-Frame α β γ) :
  UUω
  where
  field
    large-subposet-Large-Subframe :
      Large-Subposet δ (large-poset-Large-Frame F)
    is-closed-under-meets-Large-Subframe :
      is-closed-under-meets-Large-Subposet
        ( large-meet-semilattice-Large-Frame F)
        ( large-subposet-Large-Subframe)
    contains-top-Large-Subframe :
      contains-top-Large-Subposet
        ( large-meet-semilattice-Large-Frame F)
        ( large-subposet-Large-Subframe)
    is-closed-under-sup-Large-Subframe :
      is-closed-under-sup-Large-Subposet
        ( large-suplattice-Large-Frame F)
        ( large-subposet-Large-Subframe)

open Large-Subframe public

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  {δ : Level → Level} (F : Large-Frame α β γ) (S : Large-Subframe δ F)
  where

  large-poset-Large-Subframe :
    Large-Poset (λ l → α l ⊔ δ l) β
  large-poset-Large-Subframe =
    large-poset-Large-Subposet
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  large-subpreorder-Large-Subframe :
    Large-Subpreorder δ (large-preorder-Large-Frame F)
  large-subpreorder-Large-Subframe =
    large-subpreorder-Large-Subposet (large-subposet-Large-Subframe S)

  large-preorder-Large-Subframe :
    Large-Preorder (λ l → α l ⊔ δ l) (λ l1 l2 → β l1 l2)
  large-preorder-Large-Subframe =
    large-preorder-Large-Subposet
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  is-in-Large-Subframe :
    {l1 : Level} → type-Large-Frame F l1 → UU (δ l1)
  is-in-Large-Subframe =
    is-in-Large-Subposet
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  type-Large-Subframe : (l1 : Level) → UU (α l1 ⊔ δ l1)
  type-Large-Subframe =
    type-Large-Subposet
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  leq-Large-Subframe-Prop :
    Large-Relation-Prop (λ l → α l ⊔ δ l) β type-Large-Subframe
  leq-Large-Subframe-Prop =
    leq-Large-Subposet-Prop
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  leq-Large-Subframe :
    Large-Relation (λ l → α l ⊔ δ l) β type-Large-Subframe
  leq-Large-Subframe =
    leq-Large-Subposet
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  is-prop-leq-Large-Subframe :
    is-prop-Large-Relation type-Large-Subframe leq-Large-Subframe
  is-prop-leq-Large-Subframe =
    is-prop-leq-Large-Subposet
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  refl-leq-Large-Subframe :
    is-large-reflexive type-Large-Subframe leq-Large-Subframe
  refl-leq-Large-Subframe =
    refl-leq-Large-Subposet
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  transitive-leq-Large-Subframe :
    is-large-transitive type-Large-Subframe leq-Large-Subframe
  transitive-leq-Large-Subframe =
    transitive-leq-Large-Subposet
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  antisymmetric-leq-Large-Subframe :
    is-large-antisymmetric type-Large-Subframe leq-Large-Subframe
  antisymmetric-leq-Large-Subframe =
    antisymmetric-leq-Large-Subposet
      ( large-poset-Large-Frame F)
      ( large-subposet-Large-Subframe S)

  is-closed-under-sim-Large-Subframe :
    {l1 l2 : Level}
    (x : type-Large-Frame F l1)
    (y : type-Large-Frame F l2) →
    leq-Large-Frame F x y →
    leq-Large-Frame F y x →
    is-in-Large-Subframe x →
    is-in-Large-Subframe y
  is-closed-under-sim-Large-Subframe =
    is-closed-under-sim-Large-Subposet
      ( large-subposet-Large-Subframe S)

  meet-Large-Subframe :
    {l1 l2 : Level}
    (x : type-Large-Subframe l1)
    (y : type-Large-Subframe l2) →
    type-Large-Subframe (l1 ⊔ l2)
  pr1 (meet-Large-Subframe (x , p) (y , q)) =
    meet-Large-Frame F x y
  pr2 (meet-Large-Subframe (x , p) (y , q)) =
    is-closed-under-meets-Large-Subframe S x y p q

  is-greatest-binary-lower-bound-meet-Large-Subframe :
    {l1 l2 : Level}
    (x : type-Large-Subframe l1)
    (y : type-Large-Subframe l2) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Large-Subframe)
      ( x)
      ( y)
      ( meet-Large-Subframe x y)
  is-greatest-binary-lower-bound-meet-Large-Subframe
    (x , p) (y , q) (z , r) =
    is-greatest-binary-lower-bound-meet-Large-Frame F x y z

  has-meets-Large-Subframe :
    has-meets-Large-Poset
      ( large-poset-Large-Subframe)
  meet-has-meets-Large-Poset
    has-meets-Large-Subframe =
    meet-Large-Subframe
  is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
    has-meets-Large-Subframe =
    is-greatest-binary-lower-bound-meet-Large-Subframe

  top-Large-Subframe :
    type-Large-Subframe lzero
  pr1 top-Large-Subframe = top-Large-Frame F
  pr2 top-Large-Subframe = contains-top-Large-Subframe S

  is-top-element-top-Large-Subframe :
    {l1 : Level} (x : type-Large-Subframe l1) →
    leq-Large-Subframe x top-Large-Subframe
  is-top-element-top-Large-Subframe (x , p) =
    is-top-element-top-Large-Frame F x

  has-top-element-Large-Subframe :
    has-top-element-Large-Poset
      ( large-poset-Large-Subframe)
  top-has-top-element-Large-Poset
    has-top-element-Large-Subframe =
    top-Large-Subframe
  is-top-element-top-has-top-element-Large-Poset
    has-top-element-Large-Subframe =
    is-top-element-top-Large-Subframe

  is-large-meet-semilattice-Large-Subframe :
    is-large-meet-semilattice-Large-Poset
      ( large-poset-Large-Subframe)
  has-meets-is-large-meet-semilattice-Large-Poset
    is-large-meet-semilattice-Large-Subframe =
    has-meets-Large-Subframe
  has-top-element-is-large-meet-semilattice-Large-Poset
    is-large-meet-semilattice-Large-Subframe =
    has-top-element-Large-Subframe

  large-meet-semilattice-Large-Subframe :
    Large-Meet-Semilattice (λ l → α l ⊔ δ l) β
  large-poset-Large-Meet-Semilattice
    large-meet-semilattice-Large-Subframe =
    large-poset-Large-Subframe
  is-large-meet-semilattice-Large-Meet-Semilattice
    large-meet-semilattice-Large-Subframe =
    is-large-meet-semilattice-Large-Subframe

  sup-Large-Subframe :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Subframe l2) →
    type-Large-Subframe (γ ⊔ l1 ⊔ l2)
  pr1 (sup-Large-Subframe x) = sup-Large-Frame F (pr1 ∘ x)
  pr2 (sup-Large-Subframe x) =
    is-closed-under-sup-Large-Subframe S
      ( pr1 ∘ x)
      ( pr2 ∘ x)

  is-least-upper-bound-sup-Large-Subframe :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Subframe l2) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Subframe)
      ( x)
      ( sup-Large-Subframe x)
  is-least-upper-bound-sup-Large-Subframe x y =
    is-least-upper-bound-sup-Large-Frame F (pr1 ∘ x) (pr1 y)

  is-large-suplattice-Large-Subframe :
    is-large-suplattice-Large-Poset γ (large-poset-Large-Subframe)
  sup-has-least-upper-bound-family-of-elements-Large-Poset
    ( is-large-suplattice-Large-Subframe x) =
    sup-Large-Subframe x
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset
    ( is-large-suplattice-Large-Subframe x) =
    is-least-upper-bound-sup-Large-Subframe x

  large-suplattice-Large-Subframe :
    Large-Suplattice (λ l → α l ⊔ δ l) β γ
  large-poset-Large-Suplattice
    large-suplattice-Large-Subframe =
    large-poset-Large-Subframe
  is-large-suplattice-Large-Suplattice
    large-suplattice-Large-Subframe =
    is-large-suplattice-Large-Subframe

  distributive-meet-sup-Large-Subframe :
    {l1 l2 l3 : Level} (x : type-Large-Subframe l1)
    {I : UU l2} (y : I → type-Large-Subframe l3) →
    meet-Large-Subframe x (sup-Large-Subframe y) ＝
    sup-Large-Subframe (λ i → meet-Large-Subframe x (y i))
  distributive-meet-sup-Large-Subframe x y =
    eq-type-subtype
      ( large-subpreorder-Large-Subframe)
      ( distributive-meet-sup-Large-Frame F (pr1 x) (pr1 ∘ y))

  large-frame-Large-Subframe :
    Large-Frame (λ l → α l ⊔ δ l) β γ
  large-poset-Large-Frame
    large-frame-Large-Subframe =
    large-poset-Large-Subframe
  is-large-meet-semilattice-Large-Frame
    large-frame-Large-Subframe =
    is-large-meet-semilattice-Large-Subframe
  is-large-suplattice-Large-Frame
    large-frame-Large-Subframe =
    is-large-suplattice-Large-Subframe
  distributive-meet-sup-Large-Frame
    large-frame-Large-Subframe =
    distributive-meet-sup-Large-Subframe
```
