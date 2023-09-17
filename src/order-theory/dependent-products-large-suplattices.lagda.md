# Dependent products of large suplattices

```agda
module order-theory.dependent-products-large-suplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.sets
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
```

</details>

## Idea

Families of least upper bounds of families of elements in dependent products of
large posets are again least upper bounds. Therefore it follows that dependent
products of large suplattices are again large suplattices.

## Definitions

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  {l1 : Level} {I : UU l1} (L : I → Large-Suplattice α β γ)
  where

  large-poset-Π-Large-Suplattice :
    Large-Poset (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-poset-Π-Large-Suplattice =
    Π-Large-Poset (λ i → large-poset-Large-Suplattice (L i))

  is-large-suplattice-Π-Large-Suplattice :
    is-large-suplattice-Large-Poset γ large-poset-Π-Large-Suplattice
  sup-has-least-upper-bound-family-of-elements-Large-Poset
    ( is-large-suplattice-Π-Large-Suplattice {l2} {l3} {J} a) i =
    sup-Large-Suplattice (L i) (λ j → a j i)
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset
    ( is-large-suplattice-Π-Large-Suplattice {l2} {l3} {J} a) =
    is-least-upper-bound-Π-Large-Poset
      ( λ i → large-poset-Large-Suplattice (L i))
      ( a)
      ( λ i → sup-Large-Suplattice (L i) (λ j → a j i))
      ( λ i →
        is-least-upper-bound-sup-Large-Suplattice (L i) (λ j → a j i))

  Π-Large-Suplattice :
    Large-Suplattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1) γ
  large-poset-Large-Suplattice Π-Large-Suplattice =
    large-poset-Π-Large-Suplattice
  is-large-suplattice-Large-Suplattice Π-Large-Suplattice =
    is-large-suplattice-Π-Large-Suplattice

  set-Π-Large-Suplattice : (l : Level) → Set (α l ⊔ l1)
  set-Π-Large-Suplattice =
    set-Large-Suplattice Π-Large-Suplattice

  type-Π-Large-Suplattice : (l : Level) → UU (α l ⊔ l1)
  type-Π-Large-Suplattice =
    type-Large-Suplattice Π-Large-Suplattice

  is-set-type-Π-Large-Suplattice :
    {l : Level} → is-set (type-Π-Large-Suplattice l)
  is-set-type-Π-Large-Suplattice =
    is-set-type-Large-Suplattice Π-Large-Suplattice

  leq-Π-Large-Suplattice-Prop :
    Large-Relation-Prop
      ( λ l2 → α l2 ⊔ l1)
      ( λ l2 l3 → β l2 l3 ⊔ l1)
      ( type-Π-Large-Suplattice)
  leq-Π-Large-Suplattice-Prop =
    leq-Large-Suplattice-Prop Π-Large-Suplattice

  leq-Π-Large-Suplattice :
    {l2 l3 : Level}
    (x : type-Π-Large-Suplattice l2) (y : type-Π-Large-Suplattice l3) →
    UU (β l2 l3 ⊔ l1)
  leq-Π-Large-Suplattice =
    leq-Large-Suplattice Π-Large-Suplattice

  is-prop-leq-Π-Large-Suplattice :
    is-prop-Large-Relation type-Π-Large-Suplattice leq-Π-Large-Suplattice
  is-prop-leq-Π-Large-Suplattice =
    is-prop-leq-Large-Suplattice Π-Large-Suplattice

  refl-leq-Π-Large-Suplattice :
    is-large-reflexive type-Π-Large-Suplattice leq-Π-Large-Suplattice
  refl-leq-Π-Large-Suplattice =
    refl-leq-Large-Suplattice Π-Large-Suplattice

  antisymmetric-leq-Π-Large-Suplattice :
    is-large-antisymmetric type-Π-Large-Suplattice leq-Π-Large-Suplattice
  antisymmetric-leq-Π-Large-Suplattice =
    antisymmetric-leq-Large-Suplattice Π-Large-Suplattice

  transitive-leq-Π-Large-Suplattice :
    is-large-transitive type-Π-Large-Suplattice leq-Π-Large-Suplattice
  transitive-leq-Π-Large-Suplattice =
    transitive-leq-Large-Suplattice Π-Large-Suplattice

  sup-Π-Large-Suplattice :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Suplattice l3) →
    type-Π-Large-Suplattice (γ ⊔ l2 ⊔ l3)
  sup-Π-Large-Suplattice =
    sup-Large-Suplattice Π-Large-Suplattice

  is-upper-bound-family-of-elements-Π-Large-Suplattice :
    {l2 l3 l4 : Level} {J : UU l2} (x : J → type-Π-Large-Suplattice l3)
    (y : type-Π-Large-Suplattice l4) → UU (β l3 l4 ⊔ l1 ⊔ l2)
  is-upper-bound-family-of-elements-Π-Large-Suplattice =
    is-upper-bound-family-of-elements-Large-Suplattice Π-Large-Suplattice

  is-least-upper-bound-family-of-elements-Π-Large-Suplattice :
    {l2 l3 l4 : Level} {J : UU l2} (x : J → type-Π-Large-Suplattice l3) →
    type-Π-Large-Suplattice l4 → UUω
  is-least-upper-bound-family-of-elements-Π-Large-Suplattice =
    is-least-upper-bound-family-of-elements-Large-Suplattice Π-Large-Suplattice

  is-least-upper-bound-sup-Π-Large-Suplattice :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Suplattice l3) →
    is-least-upper-bound-family-of-elements-Π-Large-Suplattice x
      ( sup-Π-Large-Suplattice x)
  is-least-upper-bound-sup-Π-Large-Suplattice =
    is-least-upper-bound-sup-Large-Suplattice Π-Large-Suplattice
```
