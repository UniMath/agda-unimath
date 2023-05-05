# Subpreorders

```agda
module order-theory.subpreorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Definition

### Subpreorders

```agda
module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2) (S : element-Preorder X → Prop l3)
  where

  element-Subpreorder : UU (l1 ⊔ l3)
  element-Subpreorder = type-subtype S

  eq-element-Subpreorder :
    (x y : element-Subpreorder) → Id (pr1 x) (pr1 y) → Id x y
  eq-element-Subpreorder x y = eq-type-subtype S

  leq-Subpreorder-Prop : (x y : element-Subpreorder) → Prop l2
  leq-Subpreorder-Prop x y = leq-Preorder-Prop X (pr1 x) (pr1 y)

  leq-Subpreorder : (x y : element-Subpreorder) → UU l2
  leq-Subpreorder x y = type-Prop (leq-Subpreorder-Prop x y)

  is-prop-leq-Subpreorder :
    (x y : element-Subpreorder) → is-prop (leq-Subpreorder x y)
  is-prop-leq-Subpreorder x y =
    is-prop-type-Prop (leq-Subpreorder-Prop x y)

  refl-leq-Subpreorder : (x : element-Subpreorder) → leq-Subpreorder x x
  refl-leq-Subpreorder x = refl-leq-Preorder X (pr1 x)

  transitive-leq-Subpreorder :
    (x y z : element-Subpreorder) →
    leq-Subpreorder y z → leq-Subpreorder x y → leq-Subpreorder x z
  transitive-leq-Subpreorder x y z =
    transitive-leq-Preorder X (pr1 x) (pr1 y) (pr1 z)

  Subpreorder : Preorder (l1 ⊔ l3) l2
  pr1 Subpreorder = element-Subpreorder
  pr1 (pr2 Subpreorder) = leq-Subpreorder-Prop
  pr1 (pr2 (pr2 Subpreorder)) = refl-leq-Subpreorder
  pr2 (pr2 (pr2 Subpreorder)) = transitive-leq-Subpreorder
```

### Inclusions of subpreorders

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  module _
    {l3 l4 : Level} (S : element-Preorder X → Prop l3)
    (T : element-Preorder X → Prop l4)
    where

    inclusion-Subpreorder-Prop : Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-Subpreorder-Prop =
      Π-Prop (element-Preorder X) (λ x → hom-Prop (S x) (T x))

    inclusion-Subpreorder : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-Subpreorder = type-Prop inclusion-Subpreorder-Prop

    is-prop-inclusion-Subpreorder : is-prop inclusion-Subpreorder
    is-prop-inclusion-Subpreorder =
      is-prop-type-Prop inclusion-Subpreorder-Prop

  refl-inclusion-Subpreorder :
    {l3 : Level} (S : element-Preorder X → Prop l3) →
    inclusion-Subpreorder S S
  refl-inclusion-Subpreorder S x = id

  transitive-inclusion-Subpreorder :
    {l3 l4 l5 : Level} (S : element-Preorder X → Prop l3)
    (T : element-Preorder X → Prop l4)
    (U : element-Preorder X → Prop l5) →
    inclusion-Subpreorder T U → inclusion-Subpreorder S T →
    inclusion-Subpreorder S U
  transitive-inclusion-Subpreorder S T U g f x = (g x) ∘ (f x)

  Sub-Preorder : (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (Sub-Preorder l) = element-Preorder X → Prop l
  pr1 (pr2 (Sub-Preorder l)) = inclusion-Subpreorder-Prop
  pr1 (pr2 (pr2 (Sub-Preorder l))) = refl-inclusion-Subpreorder
  pr2 (pr2 (pr2 (Sub-Preorder l))) = transitive-inclusion-Subpreorder
```
