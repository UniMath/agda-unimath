# Subpreorders

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.subpreorders
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations funext
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.propositions funext
open import foundation.subtypes funext
open import foundation.universe-levels

open import order-theory.preorders funext
```

</details>

## Idea

A **subpreorder** of a preorder `P` is a subtype of `P`. By restriction of the
ordering on `P`, the subpreorder inherits the structure of a preorder.

## Definition

### Subpreorders

```agda
Subpreorder :
  {l1 l2 : Level} (l3 : Level) → Preorder l1 l2 → UU (l1 ⊔ lsuc l3)
Subpreorder l3 P = subtype l3 (type-Preorder P)

module _
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (S : Subpreorder l3 P)
  where

  type-Subpreorder : UU (l1 ⊔ l3)
  type-Subpreorder = type-subtype S

  eq-type-Subpreorder :
    (x y : type-Subpreorder) → Id (pr1 x) (pr1 y) → Id x y
  eq-type-Subpreorder x y = eq-type-subtype S

  leq-Subpreorder-Prop : (x y : type-Subpreorder) → Prop l2
  leq-Subpreorder-Prop x y = leq-prop-Preorder P (pr1 x) (pr1 y)

  leq-Subpreorder : (x y : type-Subpreorder) → UU l2
  leq-Subpreorder x y = type-Prop (leq-Subpreorder-Prop x y)

  is-prop-leq-Subpreorder :
    (x y : type-Subpreorder) → is-prop (leq-Subpreorder x y)
  is-prop-leq-Subpreorder x y =
    is-prop-type-Prop (leq-Subpreorder-Prop x y)

  refl-leq-Subpreorder : is-reflexive leq-Subpreorder
  refl-leq-Subpreorder x = refl-leq-Preorder P (pr1 x)

  transitive-leq-Subpreorder : is-transitive leq-Subpreorder
  transitive-leq-Subpreorder x y z =
    transitive-leq-Preorder P (pr1 x) (pr1 y) (pr1 z)

  preorder-Subpreorder : Preorder (l1 ⊔ l3) l2
  pr1 preorder-Subpreorder = type-Subpreorder
  pr1 (pr2 preorder-Subpreorder) = leq-Subpreorder-Prop
  pr1 (pr2 (pr2 preorder-Subpreorder)) = refl-leq-Subpreorder
  pr2 (pr2 (pr2 preorder-Subpreorder)) = transitive-leq-Subpreorder
```

### Inclusions of subpreorders

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  module _
    {l3 l4 : Level} (S : type-Preorder P → Prop l3)
    (T : type-Preorder P → Prop l4)
    where

    inclusion-prop-Subpreorder : Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-prop-Subpreorder =
      Π-Prop (type-Preorder P) (λ x → hom-Prop (S x) (T x))

    inclusion-Subpreorder : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-Subpreorder = type-Prop inclusion-prop-Subpreorder

    is-prop-inclusion-Subpreorder : is-prop inclusion-Subpreorder
    is-prop-inclusion-Subpreorder =
      is-prop-type-Prop inclusion-prop-Subpreorder

  refl-inclusion-Subpreorder :
    {l3 : Level} → is-reflexive (inclusion-Subpreorder {l3})
  refl-inclusion-Subpreorder S x = id

  transitive-inclusion-Subpreorder :
    {l3 l4 l5 : Level} (S : type-Preorder P → Prop l3)
    (T : type-Preorder P → Prop l4)
    (U : type-Preorder P → Prop l5) →
    inclusion-Subpreorder T U →
    inclusion-Subpreorder S T →
    inclusion-Subpreorder S U
  transitive-inclusion-Subpreorder S T U g f x = (g x) ∘ (f x)

  Sub-Preorder : (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (Sub-Preorder l) = type-Preorder P → Prop l
  pr1 (pr2 (Sub-Preorder l)) = inclusion-prop-Subpreorder
  pr1 (pr2 (pr2 (Sub-Preorder l))) = refl-inclusion-Subpreorder
  pr2 (pr2 (pr2 (Sub-Preorder l))) = transitive-inclusion-Subpreorder
```
