# Large subsuplattices

```agda
module order-theory.large-subsuplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-subposets
open import order-theory.large-suplattices
```

</details>

## Idea

A **large subsuplattice** of a
[large suplattice](order-theory.large-suplattices.md) is a large subposet which
is closed under suprema.

## Definition

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level} {δ : Level}
  (L : Large-Suplattice α β δ)
  where

  is-closed-under-sup-Large-Subposet :
    Large-Subposet γ (large-poset-Large-Suplattice L) → UUω
  is-closed-under-sup-Large-Subposet S =
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Suplattice L l2) →
    ((i : I) → is-in-Large-Subposet (large-poset-Large-Suplattice L) S (x i)) →
    is-in-Large-Subposet
      ( large-poset-Large-Suplattice L)
      ( S)
      ( sup-Large-Suplattice L x)

record
  Large-Subsuplattice
  {α : Level → Level} {β : Level → Level → Level} {δ : Level}
  (γ : Level → Level)
  (L : Large-Suplattice α β δ) :
  UUω
  where
  field
    large-subposet-Large-Subsuplattice :
      Large-Subposet γ (large-poset-Large-Suplattice L)
    is-closed-under-sup-Large-Subsuplattice :
      is-closed-under-sup-Large-Subposet L (large-subposet-Large-Subsuplattice)

open Large-Subsuplattice public

module _
  {α γ : Level → Level} {β : Level → Level → Level} {δ : Level}
  (P : Large-Suplattice α β δ) (S : Large-Subsuplattice γ P)
  where

  large-poset-Large-Subsuplattice :
    Large-Poset (λ l → α l ⊔ γ l) (λ l1 l2 → β l1 l2)
  large-poset-Large-Subsuplattice =
    large-poset-Large-Subposet
      ( large-poset-Large-Suplattice P)
      ( large-subposet-Large-Subsuplattice S)

  is-in-Large-Subsuplattice :
    {l1 : Level} → type-Large-Suplattice P l1 → UU (γ l1)
  is-in-Large-Subsuplattice =
    is-in-Large-Subposet
      ( large-poset-Large-Suplattice P)
      ( large-subposet-Large-Subsuplattice S)

  type-Large-Subsuplattice : (l1 : Level) → UU (α l1 ⊔ γ l1)
  type-Large-Subsuplattice =
    type-Large-Subposet
      ( large-poset-Large-Suplattice P)
      ( large-subposet-Large-Subsuplattice S)

  leq-Large-Subsuplattice-Prop :
    {l1 l2 : Level} →
    type-Large-Subsuplattice l1 → type-Large-Subsuplattice l2 → Prop (β l1 l2)
  leq-Large-Subsuplattice-Prop =
    leq-Large-Subposet-Prop
      ( large-poset-Large-Suplattice P)
      ( large-subposet-Large-Subsuplattice S)

  leq-Large-Subsuplattice :
    {l1 l2 : Level} →
    type-Large-Subsuplattice l1 → type-Large-Subsuplattice l2 → UU (β l1 l2)
  leq-Large-Subsuplattice =
    leq-Large-Subposet
      ( large-poset-Large-Suplattice P)
      ( large-subposet-Large-Subsuplattice S)

  is-prop-leq-Large-Subsuplattice :
    {l1 l2 : Level} →
    (x : type-Large-Subsuplattice l1) (y : type-Large-Subsuplattice l2) →
    is-prop (leq-Large-Subsuplattice x y)
  is-prop-leq-Large-Subsuplattice =
    is-prop-leq-Large-Subposet
      ( large-poset-Large-Suplattice P)
      ( large-subposet-Large-Subsuplattice S)

  refl-leq-Large-Subsuplattice :
    {l1 : Level} → is-reflexive (leq-Large-Subsuplattice {l1})
  refl-leq-Large-Subsuplattice =
    refl-leq-Large-Subposet
      ( large-poset-Large-Suplattice P)
      ( large-subposet-Large-Subsuplattice S)

  transitive-leq-Large-Subsuplattice :
    {l1 l2 l3 : Level}
    (x : type-Large-Subsuplattice l1)
    (y : type-Large-Subsuplattice l2)
    (z : type-Large-Subsuplattice l3) →
    leq-Large-Subsuplattice y z →
    leq-Large-Subsuplattice x y →
    leq-Large-Subsuplattice x z
  transitive-leq-Large-Subsuplattice =
    transitive-leq-Large-Subposet
      ( large-poset-Large-Suplattice P)
      ( large-subposet-Large-Subsuplattice S)

  antisymmetric-leq-Large-Subsuplattice :
    {l1 : Level} → is-antisymmetric (leq-Large-Subsuplattice {l1})
  antisymmetric-leq-Large-Subsuplattice =
    antisymmetric-leq-Large-Subposet
      ( large-poset-Large-Suplattice P)
      ( large-subposet-Large-Subsuplattice S)

  is-closed-under-sim-Large-Subsuplattice :
    {l1 l2 : Level}
    (x : type-Large-Suplattice P l1)
    (y : type-Large-Suplattice P l2) →
    leq-Large-Suplattice P x y →
    leq-Large-Suplattice P y x →
    is-in-Large-Subsuplattice x → is-in-Large-Subsuplattice y
  is-closed-under-sim-Large-Subsuplattice =
    is-closed-under-sim-Large-Subposet
      ( large-subposet-Large-Subsuplattice S)
```
