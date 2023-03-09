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

  element-sub-Preorder : UU (l1 ⊔ l3)
  element-sub-Preorder = type-subtype S

  eq-element-sub-Preorder :
    (x y : element-sub-Preorder) → Id (pr1 x) (pr1 y) → Id x y
  eq-element-sub-Preorder x y = eq-type-subtype S

  leq-sub-preorder-Prop : (x y : element-sub-Preorder) → Prop l2
  leq-sub-preorder-Prop x y = leq-preorder-Prop X (pr1 x) (pr1 y)

  leq-sub-Preorder : (x y : element-sub-Preorder) → UU l2
  leq-sub-Preorder x y = type-Prop (leq-sub-preorder-Prop x y)

  is-prop-leq-sub-Preorder :
    (x y : element-sub-Preorder) → is-prop (leq-sub-Preorder x y)
  is-prop-leq-sub-Preorder x y =
    is-prop-type-Prop (leq-sub-preorder-Prop x y)

  refl-leq-sub-Preorder : (x : element-sub-Preorder) → leq-sub-Preorder x x
  refl-leq-sub-Preorder x = refl-leq-Preorder X (pr1 x)

  transitive-leq-sub-Preorder :
    (x y z : element-sub-Preorder) →
    leq-sub-Preorder y z → leq-sub-Preorder x y → leq-sub-Preorder x z
  transitive-leq-sub-Preorder x y z =
    transitive-leq-Preorder X (pr1 x) (pr1 y) (pr1 z)

  sub-Preorder : Preorder (l1 ⊔ l3) l2
  pr1 sub-Preorder = element-sub-Preorder
  pr1 (pr2 sub-Preorder) = leq-sub-preorder-Prop
  pr1 (pr2 (pr2 sub-Preorder)) = refl-leq-sub-Preorder
  pr2 (pr2 (pr2 sub-Preorder)) = transitive-leq-sub-Preorder
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

    inclusion-sub-preorder-Prop : Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-sub-preorder-Prop =
      Π-Prop (element-Preorder X) (λ x → hom-Prop (S x) (T x))

    inclusion-sub-Preorder : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-sub-Preorder = type-Prop inclusion-sub-preorder-Prop

    is-prop-inclusion-sub-Preorder : is-prop inclusion-sub-Preorder
    is-prop-inclusion-sub-Preorder =
      is-prop-type-Prop inclusion-sub-preorder-Prop

  refl-inclusion-sub-Preorder :
    {l3 : Level} (S : element-Preorder X → Prop l3) →
    inclusion-sub-Preorder S S
  refl-inclusion-sub-Preorder S x = id

  transitive-inclusion-sub-Preorder :
    {l3 l4 l5 : Level} (S : element-Preorder X → Prop l3)
    (T : element-Preorder X → Prop l4)
    (U : element-Preorder X → Prop l5) →
    inclusion-sub-Preorder T U → inclusion-sub-Preorder S T →
    inclusion-sub-Preorder S U
  transitive-inclusion-sub-Preorder S T U g f x = (g x) ∘ (f x)

  Sub-Preorder : (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (Sub-Preorder l) = element-Preorder X → Prop l
  pr1 (pr2 (Sub-Preorder l)) = inclusion-sub-preorder-Prop
  pr1 (pr2 (pr2 (Sub-Preorder l))) = refl-inclusion-sub-Preorder
  pr2 (pr2 (pr2 (Sub-Preorder l))) = transitive-inclusion-sub-Preorder
```
