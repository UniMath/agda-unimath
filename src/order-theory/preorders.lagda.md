# Preorders

```agda
module order-theory.preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A **preorder** is a type equipped with a reflexive, transitive relation that is
valued in propositions.

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

  type-Preorder : UU l1
  type-Preorder = pr1 X

  leq-Preorder-Prop : (x y : type-Preorder) → Prop l2
  leq-Preorder-Prop = pr1 (pr2 X)

  leq-Preorder : (x y : type-Preorder) → UU l2
  leq-Preorder x y = type-Prop (leq-Preorder-Prop x y)

  is-prop-leq-Preorder : (x y : type-Preorder) → is-prop (leq-Preorder x y)
  is-prop-leq-Preorder x y = is-prop-type-Prop (leq-Preorder-Prop x y)

  concatenate-eq-leq-Preorder :
    {x y z : type-Preorder} → x ＝ y → leq-Preorder y z → leq-Preorder x z
  concatenate-eq-leq-Preorder refl = id

  concatenate-leq-eq-Preorder :
    {x y z : type-Preorder} → leq-Preorder x y → y ＝ z → leq-Preorder x z
  concatenate-leq-eq-Preorder H refl = H

  le-Preorder-Prop : (x y : type-Preorder) → Prop (l1 ⊔ l2)
  le-Preorder-Prop x y =
    prod-Prop (¬ (x ＝ y) , is-prop-neg) (leq-Preorder-Prop x y)

  le-Preorder : (x y : type-Preorder) → UU (l1 ⊔ l2)
  le-Preorder x y = type-Prop (le-Preorder-Prop x y)

  is-prop-le-Preorder :
    (x y : type-Preorder) → is-prop (le-Preorder x y)
  is-prop-le-Preorder x y =
    is-prop-type-Prop (le-Preorder-Prop x y)

  refl-leq-Preorder : (x : type-Preorder) → leq-Preorder x x
  refl-leq-Preorder = pr1 (pr2 (pr2 X))

  transitive-leq-Preorder :
    (x y z : type-Preorder) →
    leq-Preorder y z → leq-Preorder x y → leq-Preorder x z
  transitive-leq-Preorder = pr2 (pr2 (pr2 X))
```

## Reasoning with inequalities in preorders

Inequalities in preorders can be constructed by equational reasoning as follows:

```text
calculate-in-Preorder X
  chain-of-inequalities
  x ≤ y
      by ineq-1
      in-Preorder X
    ≤ z
      by ineq-2
      in-Preorder X
    ≤ v
      by ineq-3
      in-Preorder X
```

Note, however, that in our setup of equational reasoning with inequalities it is
not possible to mix inequalities with equalities or strict inequalities.

```agda
infixl 1 calculate-in-Preorder_chain-of-inequalities_
infixl 0 step-calculate-in-Preorder

calculate-in-Preorder_chain-of-inequalities_ :
  {l1 l2 : Level} (X : Preorder l1 l2)
  (x : type-Preorder X) → leq-Preorder X x x
calculate-in-Preorder_chain-of-inequalities_ = refl-leq-Preorder

step-calculate-in-Preorder :
  {l1 l2 : Level} (X : Preorder l1 l2)
  {x y : type-Preorder X} → leq-Preorder X x y →
  (z : type-Preorder X) → leq-Preorder X y z → leq-Preorder X x z
step-calculate-in-Preorder X {x} {y} u z v =
  transitive-leq-Preorder X x y z v u

syntax step-calculate-in-Preorder X u z v = u ≤ z by v in-Preorder X
```
