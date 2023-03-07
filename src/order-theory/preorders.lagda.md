# Preorders

```agda
module order-theory.preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A preorder is a type equipped with a reflexive, transitive relation that is valued in propositions.

## Definition

```agda
Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Preorder l1 l2 =
  Σ ( UU l1)
    ( λ X →
      Σ ( X → X → Prop l2)
        ( λ R →
          ( (x : X) → type-Prop (R x x)) ×
          ( (x y z : X) →
            type-Prop (R y z) → type-Prop (R x y) → type-Prop (R x z))))

module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  element-Preorder : UU l1
  element-Preorder = pr1 X

  leq-preorder-Prop : (x y : element-Preorder) → Prop l2
  leq-preorder-Prop = pr1 (pr2 X)

  leq-Preorder : (x y : element-Preorder) → UU l2
  leq-Preorder x y = type-Prop (leq-preorder-Prop x y)

  is-prop-leq-Preorder : (x y : element-Preorder) → is-prop (leq-Preorder x y)
  is-prop-leq-Preorder x y = is-prop-type-Prop (leq-preorder-Prop x y)

  refl-leq-Preorder : (x : element-Preorder) → leq-Preorder x x
  refl-leq-Preorder = pr1 (pr2 (pr2 X))

  transitive-leq-Preorder :
    (x y z : element-Preorder) →
    leq-Preorder y z → leq-Preorder x y → leq-Preorder x z
  transitive-leq-Preorder = pr2 (pr2 (pr2 X))
```
