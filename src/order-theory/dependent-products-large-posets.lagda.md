# Dependent products of large posets

```agda
module order-theory.dependent-products-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.large-binary-relations
open import foundation.universe-levels

open import order-theory.dependent-products-large-preorders
open import order-theory.large-posets
open import order-theory.large-preorders
```

</details>

## Idea

Given a family `P : I → Large-Poset α β` indexed by a type `I : UU l`, the
dependent product of the large posets `P i` is again a large poset.

## Definitions

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (P : I → Large-Poset α β)
  where

  large-preorder-Π-Large-Poset :
    Large-Preorder (λ l1 → α l1 ⊔ l) (λ l1 l2 → β l1 l2 ⊔ l)
  large-preorder-Π-Large-Poset =
    Π-Large-Preorder (λ i → large-preorder-Large-Poset (P i))

  type-Π-Large-Poset : (l1 : Level) → UU (α l1 ⊔ l)
  type-Π-Large-Poset =
    type-Π-Large-Preorder (λ i → large-preorder-Large-Poset (P i))

  leq-prop-Π-Large-Poset :
    Large-Relation-Prop
      ( λ l1 l2 → β l1 l2 ⊔ l)
      ( type-Π-Large-Poset)
  leq-prop-Π-Large-Poset =
    leq-prop-Π-Large-Preorder (λ i → large-preorder-Large-Poset (P i))

  leq-Π-Large-Poset :
    Large-Relation
      ( λ l1 l2 → β l1 l2 ⊔ l)
      ( type-Π-Large-Poset)
  leq-Π-Large-Poset =
    leq-Π-Large-Preorder (λ i → large-preorder-Large-Poset (P i))

  is-prop-leq-Π-Large-Poset :
    is-prop-Large-Relation type-Π-Large-Poset leq-Π-Large-Poset
  is-prop-leq-Π-Large-Poset =
    is-prop-leq-Π-Large-Preorder (λ i → large-preorder-Large-Poset (P i))

  refl-leq-Π-Large-Poset :
    is-reflexive-Large-Relation type-Π-Large-Poset leq-Π-Large-Poset
  refl-leq-Π-Large-Poset =
    refl-leq-Π-Large-Preorder (λ i → large-preorder-Large-Poset (P i))

  transitive-leq-Π-Large-Poset :
    is-transitive-Large-Relation type-Π-Large-Poset leq-Π-Large-Poset
  transitive-leq-Π-Large-Poset =
    transitive-leq-Π-Large-Preorder (λ i → large-preorder-Large-Poset (P i))

  antisymmetric-leq-Π-Large-Poset :
    is-antisymmetric-Large-Relation type-Π-Large-Poset leq-Π-Large-Poset
  antisymmetric-leq-Π-Large-Poset x y H K =
    eq-htpy (λ i → antisymmetric-leq-Large-Poset (P i) (x i) (y i) (H i) (K i))

  Π-Large-Poset : Large-Poset (λ l1 → α l1 ⊔ l) (λ l1 l2 → β l1 l2 ⊔ l)
  large-preorder-Large-Poset Π-Large-Poset =
    large-preorder-Π-Large-Poset
  antisymmetric-leq-Large-Poset Π-Large-Poset =
    antisymmetric-leq-Π-Large-Poset
```
