# Dependent products of large meet-semilattices

```agda
module order-theory.dependent-products-large-meet-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.sets
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.top-elements-large-posets
```

</details>

## Idea

Meets in dependent products of large posets are computed pointwise. This implies
that the dependent product of a large meet-semilattice is again a large
meet-semilattice.

## Definitions

### Meets in dependent products of large posets that have meets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (P : I → Large-Poset α β)
  where

  has-meets-Π-Large-Poset :
    ((i : I) → has-meets-Large-Poset (P i)) →
    has-meets-Large-Poset (Π-Large-Poset P)
  meet-has-meets-Large-Poset (has-meets-Π-Large-Poset H) x y i =
    meet-has-meets-Large-Poset (H i) (x i) (y i)
  is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
    ( has-meets-Π-Large-Poset H) x y =
    is-greatest-binary-lower-bound-Π-Large-Poset P x y
      ( λ i → meet-has-meets-Large-Poset (H i) (x i) (y i))
      ( λ i →
        is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
          ( H i)
          ( x i)
          ( y i))
```

### Large meet-semilattices

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (L : I → Large-Meet-Semilattice α β)
  where

  large-poset-Π-Large-Meet-Semilattice :
    Large-Poset (λ l1 → α l1 ⊔ l) (λ l1 l2 → β l1 l2 ⊔ l)
  large-poset-Π-Large-Meet-Semilattice =
    Π-Large-Poset (λ i → large-poset-Large-Meet-Semilattice (L i))

  has-meets-Π-Large-Meet-Semilattice :
    has-meets-Large-Poset large-poset-Π-Large-Meet-Semilattice
  has-meets-Π-Large-Meet-Semilattice =
    has-meets-Π-Large-Poset
      ( λ i → large-poset-Large-Meet-Semilattice (L i))
      ( λ i → has-meets-Large-Meet-Semilattice (L i))

  has-top-element-Π-Large-Meet-Semilattice :
    has-top-element-Large-Poset large-poset-Π-Large-Meet-Semilattice
  has-top-element-Π-Large-Meet-Semilattice =
    has-top-element-Π-Large-Poset
      ( λ i → large-poset-Large-Meet-Semilattice (L i))
      ( λ i → has-top-element-Large-Meet-Semilattice (L i))

  is-large-meet-semilattice-Π-Large-Meet-Semilattice :
    is-large-meet-semilattice-Large-Poset
      large-poset-Π-Large-Meet-Semilattice
  has-meets-is-large-meet-semilattice-Large-Poset
    is-large-meet-semilattice-Π-Large-Meet-Semilattice =
    has-meets-Π-Large-Meet-Semilattice
  has-top-element-is-large-meet-semilattice-Large-Poset
    is-large-meet-semilattice-Π-Large-Meet-Semilattice =
    has-top-element-Π-Large-Meet-Semilattice

  Π-Large-Meet-Semilattice :
    Large-Meet-Semilattice (λ l1 → α l1 ⊔ l) (λ l1 l2 → β l1 l2 ⊔ l)
  large-poset-Large-Meet-Semilattice Π-Large-Meet-Semilattice =
    large-poset-Π-Large-Meet-Semilattice
  is-large-meet-semilattice-Large-Meet-Semilattice Π-Large-Meet-Semilattice =
    is-large-meet-semilattice-Π-Large-Meet-Semilattice

  type-Π-Large-Meet-Semilattice : (l1 : Level) → UU (α l1 ⊔ l)
  type-Π-Large-Meet-Semilattice =
    type-Large-Meet-Semilattice Π-Large-Meet-Semilattice

  set-Π-Large-Meet-Semilattice : (l1 : Level) → Set (α l1 ⊔ l)
  set-Π-Large-Meet-Semilattice =
    set-Large-Meet-Semilattice Π-Large-Meet-Semilattice

  is-set-type-Π-Large-Meet-Semilattice :
    {l : Level} → is-set (type-Π-Large-Meet-Semilattice l)
  is-set-type-Π-Large-Meet-Semilattice =
    is-set-type-Large-Meet-Semilattice Π-Large-Meet-Semilattice

  leq-Π-Large-Meet-Semilattice :
    Large-Relation
      ( λ l1 → α l1 ⊔ l)
      ( λ l1 l2 → β l1 l2 ⊔ l)
      ( type-Π-Large-Meet-Semilattice)
  leq-Π-Large-Meet-Semilattice =
    leq-Large-Meet-Semilattice Π-Large-Meet-Semilattice

  refl-leq-Π-Large-Meet-Semilattice :
    is-large-reflexive
      ( type-Π-Large-Meet-Semilattice)
      ( leq-Π-Large-Meet-Semilattice)
  refl-leq-Π-Large-Meet-Semilattice =
    refl-leq-Large-Meet-Semilattice Π-Large-Meet-Semilattice

  antisymmetric-leq-Π-Large-Meet-Semilattice :
    is-large-antisymmetric
      ( type-Π-Large-Meet-Semilattice)
      ( leq-Π-Large-Meet-Semilattice)
  antisymmetric-leq-Π-Large-Meet-Semilattice =
    antisymmetric-leq-Large-Meet-Semilattice Π-Large-Meet-Semilattice

  transitive-leq-Π-Large-Meet-Semilattice :
    is-large-transitive
      ( type-Π-Large-Meet-Semilattice)
      ( leq-Π-Large-Meet-Semilattice)
  transitive-leq-Π-Large-Meet-Semilattice =
    transitive-leq-Large-Meet-Semilattice Π-Large-Meet-Semilattice

  meet-Π-Large-Meet-Semilattice :
    {l1 l2 : Level}
    (x : type-Π-Large-Meet-Semilattice l1)
    (y : type-Π-Large-Meet-Semilattice l2) →
    type-Π-Large-Meet-Semilattice (l1 ⊔ l2)
  meet-Π-Large-Meet-Semilattice =
    meet-Large-Meet-Semilattice Π-Large-Meet-Semilattice

  is-greatest-binary-lower-bound-meet-Π-Large-Meet-Semilattice :
    {l1 l2 : Level}
    (x : type-Π-Large-Meet-Semilattice l1)
    (y : type-Π-Large-Meet-Semilattice l2) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Π-Large-Meet-Semilattice)
      ( x)
      ( y)
      ( meet-Π-Large-Meet-Semilattice x y)
  is-greatest-binary-lower-bound-meet-Π-Large-Meet-Semilattice =
    is-greatest-binary-lower-bound-meet-Large-Meet-Semilattice
      Π-Large-Meet-Semilattice

  top-Π-Large-Meet-Semilattice :
    type-Π-Large-Meet-Semilattice lzero
  top-Π-Large-Meet-Semilattice =
    top-has-top-element-Large-Poset
      has-top-element-Π-Large-Meet-Semilattice

  is-top-element-top-Π-Large-Meet-Semilattice :
    {l1 : Level} (x : type-Π-Large-Meet-Semilattice l1) →
    leq-Π-Large-Meet-Semilattice x top-Π-Large-Meet-Semilattice
  is-top-element-top-Π-Large-Meet-Semilattice =
    is-top-element-top-has-top-element-Large-Poset
      has-top-element-Π-Large-Meet-Semilattice
```
