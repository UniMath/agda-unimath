# Large meet-subsemilattices

```agda
module order-theory.large-meet-subsemilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.large-binary-relations
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-subposets
open import order-theory.top-elements-large-posets
```

</details>

## Idea

A **large meet-subsemilattice** of a
[large meet-semilattice](order-theory.large-meet-semilattices.md) `L` is a
[large subposet](order-theory.large-subposets.md) `S` of `L` that is closed
under meets and contains the top element.

## Definitions

### The predicate that a large subposet is closed under meets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (L : Large-Meet-Semilattice α β)
  (S : Large-Subposet γ (large-poset-Large-Meet-Semilattice L))
  where

  is-closed-under-meets-Large-Subposet : UUω
  is-closed-under-meets-Large-Subposet =
    {l1 l2 : Level}
    (x : type-Large-Meet-Semilattice L l1)
    (y : type-Large-Meet-Semilattice L l2) →
    is-in-Large-Subposet (large-poset-Large-Meet-Semilattice L) S x →
    is-in-Large-Subposet (large-poset-Large-Meet-Semilattice L) S y →
    is-in-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( S)
      ( meet-Large-Meet-Semilattice L x y)
```

### The predicate that a large subposet contains the top element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (L : Large-Meet-Semilattice α β)
  (S : Large-Subposet γ (large-poset-Large-Meet-Semilattice L))
  where

  contains-top-Large-Subposet : UU (γ lzero)
  contains-top-Large-Subposet =
    is-in-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( S)
      ( top-Large-Meet-Semilattice L)
```

### The predicate that a large subposet is a large meet-subsemilattice

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (L : Large-Meet-Semilattice α β)
  (S : Large-Subposet γ (large-poset-Large-Meet-Semilattice L))
  where

  record
    is-large-meet-subsemilattice-Large-Subposet : UUω
    where
    field
      is-closed-under-meets-is-large-meet-subsemilattice-Large-Subposet :
        is-closed-under-meets-Large-Subposet L S
      contains-top-is-large-meet-subsemilattice-Large-Poset :
        contains-top-Large-Subposet L S

  open is-large-meet-subsemilattice-Large-Subposet public
```

### Large meet-subsemilattices

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level → Level)
  (L : Large-Meet-Semilattice α β)
  where

  record
    Large-Meet-Subsemilattice : UUω
    where
    field
      large-subposet-Large-Meet-Subsemilattice :
        Large-Subposet γ (large-poset-Large-Meet-Semilattice L)
      is-closed-under-meets-Large-Meet-Subsemilattice :
        is-closed-under-meets-Large-Subposet L
          ( large-subposet-Large-Meet-Subsemilattice)
      contains-top-Large-Meet-Subsemilattice :
        contains-top-Large-Subposet L
          ( large-subposet-Large-Meet-Subsemilattice)

  open Large-Meet-Subsemilattice public

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (L : Large-Meet-Semilattice α β)
  (S : Large-Meet-Subsemilattice γ L)
  where

  large-poset-Large-Meet-Subsemilattice :
    Large-Poset (λ l → α l ⊔ γ l) β
  large-poset-Large-Meet-Subsemilattice =
    large-poset-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  large-preorder-Large-Meet-Subsemilattice :
    Large-Preorder (λ l → α l ⊔ γ l) (λ l1 l2 → β l1 l2)
  large-preorder-Large-Meet-Subsemilattice =
    large-preorder-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  is-in-Large-Meet-Subsemilattice :
    {l1 : Level} → type-Large-Meet-Semilattice L l1 → UU (γ l1)
  is-in-Large-Meet-Subsemilattice =
    is-in-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  type-Large-Meet-Subsemilattice : (l1 : Level) → UU (α l1 ⊔ γ l1)
  type-Large-Meet-Subsemilattice =
    type-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  leq-prop-Large-Meet-Subsemilattice :
    Large-Relation-Prop β type-Large-Meet-Subsemilattice
  leq-prop-Large-Meet-Subsemilattice =
    leq-prop-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  leq-Large-Meet-Subsemilattice :
    Large-Relation β type-Large-Meet-Subsemilattice
  leq-Large-Meet-Subsemilattice =
    leq-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  is-prop-leq-Large-Meet-Subsemilattice :
    is-prop-Large-Relation
      ( type-Large-Meet-Subsemilattice)
      ( leq-Large-Meet-Subsemilattice)
  is-prop-leq-Large-Meet-Subsemilattice =
    is-prop-leq-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  refl-leq-Large-Meet-Subsemilattice :
    is-reflexive-Large-Relation
      ( type-Large-Meet-Subsemilattice)
      ( leq-Large-Meet-Subsemilattice)
  refl-leq-Large-Meet-Subsemilattice =
    refl-leq-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  transitive-leq-Large-Meet-Subsemilattice :
    is-transitive-Large-Relation
      ( type-Large-Meet-Subsemilattice)
      ( leq-Large-Meet-Subsemilattice)
  transitive-leq-Large-Meet-Subsemilattice =
    transitive-leq-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  antisymmetric-leq-Large-Meet-Subsemilattice :
    is-antisymmetric-Large-Relation
      ( type-Large-Meet-Subsemilattice)
      ( leq-Large-Meet-Subsemilattice)
  antisymmetric-leq-Large-Meet-Subsemilattice =
    antisymmetric-leq-Large-Subposet
      ( large-poset-Large-Meet-Semilattice L)
      ( large-subposet-Large-Meet-Subsemilattice S)

  is-closed-under-sim-Large-Meet-Subsemilattice :
    {l1 l2 : Level}
    (x : type-Large-Meet-Semilattice L l1)
    (y : type-Large-Meet-Semilattice L l2) →
    leq-Large-Meet-Semilattice L x y →
    leq-Large-Meet-Semilattice L y x →
    is-in-Large-Meet-Subsemilattice x →
    is-in-Large-Meet-Subsemilattice y
  is-closed-under-sim-Large-Meet-Subsemilattice =
    is-closed-under-sim-Large-Subposet
      ( large-subposet-Large-Meet-Subsemilattice S)

  meet-Large-Meet-Subsemilattice :
    {l1 l2 : Level}
    (x : type-Large-Meet-Subsemilattice l1)
    (y : type-Large-Meet-Subsemilattice l2) →
    type-Large-Meet-Subsemilattice (l1 ⊔ l2)
  pr1 (meet-Large-Meet-Subsemilattice (x , p) (y , q)) =
    meet-Large-Meet-Semilattice L x y
  pr2 (meet-Large-Meet-Subsemilattice (x , p) (y , q)) =
    is-closed-under-meets-Large-Meet-Subsemilattice S x y p q

  is-greatest-binary-lower-bound-meet-Large-Meet-Subsemilattice :
    {l1 l2 : Level}
    (x : type-Large-Meet-Subsemilattice l1)
    (y : type-Large-Meet-Subsemilattice l2) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Large-Meet-Subsemilattice)
      ( x)
      ( y)
      ( meet-Large-Meet-Subsemilattice x y)
  is-greatest-binary-lower-bound-meet-Large-Meet-Subsemilattice
    (x , p) (y , q) (z , r) =
    is-greatest-binary-lower-bound-meet-Large-Meet-Semilattice L x y z

  has-meets-Large-Meet-Subsemilattice :
    has-meets-Large-Poset
      ( large-poset-Large-Meet-Subsemilattice)
  meet-has-meets-Large-Poset
    has-meets-Large-Meet-Subsemilattice =
    meet-Large-Meet-Subsemilattice
  is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
    has-meets-Large-Meet-Subsemilattice =
    is-greatest-binary-lower-bound-meet-Large-Meet-Subsemilattice

  top-Large-Meet-Subsemilattice :
    type-Large-Meet-Subsemilattice lzero
  pr1 top-Large-Meet-Subsemilattice = top-Large-Meet-Semilattice L
  pr2 top-Large-Meet-Subsemilattice = contains-top-Large-Meet-Subsemilattice S

  is-top-element-top-Large-Meet-Subsemilattice :
    {l1 : Level} (x : type-Large-Meet-Subsemilattice l1) →
    leq-Large-Meet-Subsemilattice x top-Large-Meet-Subsemilattice
  is-top-element-top-Large-Meet-Subsemilattice (x , p) =
    is-top-element-top-Large-Meet-Semilattice L x

  has-top-element-Large-Meet-Subsemilattice :
    has-top-element-Large-Poset
      ( large-poset-Large-Meet-Subsemilattice)
  top-has-top-element-Large-Poset
    has-top-element-Large-Meet-Subsemilattice =
    top-Large-Meet-Subsemilattice
  is-top-element-top-has-top-element-Large-Poset
    has-top-element-Large-Meet-Subsemilattice =
    is-top-element-top-Large-Meet-Subsemilattice

  is-large-meet-semilattice-Large-Meet-Subsemilattice :
    is-large-meet-semilattice-Large-Poset
      ( large-poset-Large-Meet-Subsemilattice)
  has-meets-is-large-meet-semilattice-Large-Poset
    is-large-meet-semilattice-Large-Meet-Subsemilattice =
    has-meets-Large-Meet-Subsemilattice
  has-top-element-is-large-meet-semilattice-Large-Poset
    is-large-meet-semilattice-Large-Meet-Subsemilattice =
    has-top-element-Large-Meet-Subsemilattice

  large-meet-semilattice-Large-Meet-Subsemilattice :
    Large-Meet-Semilattice (λ l → α l ⊔ γ l) β
  large-poset-Large-Meet-Semilattice
    large-meet-semilattice-Large-Meet-Subsemilattice =
    large-poset-Large-Meet-Subsemilattice
  is-large-meet-semilattice-Large-Meet-Semilattice
    large-meet-semilattice-Large-Meet-Subsemilattice =
    is-large-meet-semilattice-Large-Meet-Subsemilattice
```
