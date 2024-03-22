# Large subposets

```agda
module order-theory.large-subposets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.large-binary-relations
open import foundation.large-reflexive-relations
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-subpreorders
```

</details>

## Idea

A **large subposet** of a [large poset](order-theory.large-posets.md) `P`
consists of a subtype `S : type-Large-Poset P l1 → Prop (γ l1)` for each
universe level `l1` such that the implication

```text
  ((x ≤ y) ∧ (y ≤ x)) → (x ∈ S → y ∈ S)
```

holds for every `x y : P`. Note that for elements of the same universe level,
this is automatic by antisymmetry.

## Definition

### The predicate of being closed under similarity

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β) (S : Large-Subpreorder γ (large-preorder-Large-Poset P))
  where

  is-closed-under-sim-Large-Subpreorder : UUω
  is-closed-under-sim-Large-Subpreorder =
    {l1 l2 : Level}
    (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    leq-Large-Poset P x y → leq-Large-Poset P y x →
    is-in-Large-Subpreorder (large-preorder-Large-Poset P) S x →
    is-in-Large-Subpreorder (large-preorder-Large-Poset P) S y
```

### Large subposets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level → Level)
  (P : Large-Poset α β)
  where

  record
    Large-Subposet : UUω
    where
    field
      large-subpreorder-Large-Subposet :
        Large-Subpreorder γ (large-preorder-Large-Poset P)
      is-closed-under-sim-Large-Subposet :
        is-closed-under-sim-Large-Subpreorder P large-subpreorder-Large-Subposet

  open Large-Subposet public

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (P : Large-Poset α β) (S : Large-Subposet γ P)
  where

  large-preorder-Large-Subposet :
    Large-Preorder (λ l → α l ⊔ γ l) (λ l1 l2 → β l1 l2)
  large-preorder-Large-Subposet =
    large-preorder-Large-Subpreorder
      ( large-preorder-Large-Poset P)
      ( large-subpreorder-Large-Subposet S)

  is-in-Large-Subposet :
    {l1 : Level} → type-Large-Poset P l1 → UU (γ l1)
  is-in-Large-Subposet =
    is-in-Large-Subpreorder
      ( large-preorder-Large-Poset P)
      ( large-subpreorder-Large-Subposet S)

  type-Large-Subposet : (l1 : Level) → UU (α l1 ⊔ γ l1)
  type-Large-Subposet =
    type-Large-Subpreorder
      ( large-preorder-Large-Poset P)
      ( large-subpreorder-Large-Subposet S)

  leq-prop-Large-Subposet :
    Large-Relation-Prop β type-Large-Subposet
  leq-prop-Large-Subposet =
    leq-prop-Large-Subpreorder
      ( large-preorder-Large-Poset P)
      ( large-subpreorder-Large-Subposet S)

  leq-Large-Subposet :
    Large-Relation β type-Large-Subposet
  leq-Large-Subposet =
    leq-Large-Subpreorder
      ( large-preorder-Large-Poset P)
      ( large-subpreorder-Large-Subposet S)

  is-prop-leq-Large-Subposet :
    is-prop-Large-Relation type-Large-Subposet leq-Large-Subposet
  is-prop-leq-Large-Subposet =
    is-prop-leq-Large-Subpreorder
      ( large-preorder-Large-Poset P)
      ( large-subpreorder-Large-Subposet S)

  refl-leq-Large-Subposet :
    is-reflexive-Large-Relation type-Large-Subposet leq-Large-Subposet
  refl-leq-Large-Subposet =
    refl-leq-Large-Subpreorder
      ( large-preorder-Large-Poset P)
      ( large-subpreorder-Large-Subposet S)

  transitive-leq-Large-Subposet :
    is-transitive-Large-Relation type-Large-Subposet leq-Large-Subposet
  transitive-leq-Large-Subposet =
    transitive-leq-Large-Subpreorder
      ( large-preorder-Large-Poset P)
      ( large-subpreorder-Large-Subposet S)

  antisymmetric-leq-Large-Subposet :
    is-antisymmetric-Large-Relation type-Large-Subposet leq-Large-Subposet
  antisymmetric-leq-Large-Subposet {l1} (x , p) (y , q) H K =
    eq-type-subtype
      ( large-subpreorder-Large-Subposet S {l1})
      ( antisymmetric-leq-Large-Poset P x y H K)

  large-poset-Large-Subposet : Large-Poset (λ l → α l ⊔ γ l) β
  large-preorder-Large-Poset
    large-poset-Large-Subposet =
    large-preorder-Large-Subposet
  antisymmetric-leq-Large-Poset
    large-poset-Large-Subposet =
    antisymmetric-leq-Large-Subposet
```

### The predicate of having the same elements

```agda
module _
  {α γS γT : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β) (S : Large-Subposet γS P) (T : Large-Subposet γT P)
  where

  has-same-elements-Large-Subposet : UUω
  has-same-elements-Large-Subposet =
    {l : Level} (x : type-Large-Poset P l) →
    is-in-Large-Subposet P S x ↔ is-in-Large-Subposet P T x
```
