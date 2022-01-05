---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module order-theory.posets where

open import order-theory.preorders public
```

## Posets

```agda
Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Poset l1 l2 =
  Σ ( UU l1)
    ( λ X →
      Σ ( X → X → UU-Prop l2)
        ( λ R →
          ( ( (x : X) → type-Prop (R x x)) ×
            ( (x y z : X) →
              type-Prop (R y z) → type-Prop (R x y) → type-Prop (R x z))) ×
          ( (x y : X) → type-Prop (R x y) → type-Prop (R y x) → Id x y)))

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  element-Poset : UU l1
  element-Poset = pr1 X

  leq-Poset-Prop : (x y : element-Poset) → UU-Prop l2
  leq-Poset-Prop = pr1 (pr2 X)

  leq-Poset : (x y : element-Poset) →  UU l2
  leq-Poset x y = type-Prop (leq-Poset-Prop x y)

  is-prop-leq-Poset : (x y : element-Poset) → is-prop (leq-Poset x y)
  is-prop-leq-Poset x y = is-prop-type-Prop (leq-Poset-Prop x y)

  refl-leq-Poset : (x : element-Poset) → leq-Poset x x
  refl-leq-Poset = pr1 (pr1 (pr2 (pr2 X)))

  transitive-leq-Poset :
    (x y z : element-Poset) → leq-Poset y z → leq-Poset x y → leq-Poset x z
  transitive-leq-Poset = pr2 (pr1 (pr2 (pr2 X)))

  preorder-Poset : Preorder l1 l2
  pr1 preorder-Poset = element-Poset
  pr1 (pr2 preorder-Poset) = leq-Poset-Prop
  pr1 (pr2 (pr2 preorder-Poset)) = refl-leq-Poset
  pr2 (pr2 (pr2 preorder-Poset)) = transitive-leq-Poset

  antisymmetric-leq-Poset :
    (x y : element-Poset) → leq-Poset x y → leq-Poset y x → Id x y
  antisymmetric-leq-Poset = pr2 (pr2 (pr2 X))

  is-set-element-Poset : is-set element-Poset
  is-set-element-Poset =
    is-set-prop-in-id
      ( λ x y → leq-Poset x y × leq-Poset y x)
      ( λ x y → is-prop-prod (is-prop-leq-Poset x y) (is-prop-leq-Poset y x))
      ( λ x → pair (refl-leq-Poset x) (refl-leq-Poset x))
      ( λ {x y (pair H K) → antisymmetric-leq-Poset x y H K})

  element-poset-Set : UU-Set l1
  pr1 element-poset-Set = element-Poset
  pr2 element-poset-Set = is-set-element-Poset

  incident-Poset-Prop : (x y : element-Poset) → UU-Prop l2
  incident-Poset-Prop = incident-Preorder-Prop preorder-Poset

  incident-Poset : (x y : element-Poset) → UU l2
  incident-Poset = incident-Preorder preorder-Poset

  is-prop-incident-Poset : (x y : element-Poset) → is-prop (incident-Poset x y)
  is-prop-incident-Poset = is-prop-incident-Preorder preorder-Poset

  is-total-Poset-Prop : UU-Prop (l1 ⊔ l2)
  is-total-Poset-Prop = is-total-Preorder-Prop preorder-Poset

  is-total-Poset : UU (l1 ⊔ l2)
  is-total-Poset = is-total-Preorder preorder-Poset

  is-prop-is-total-Poset : is-prop is-total-Poset
  is-prop-is-total-Poset = is-prop-is-total-Preorder preorder-Poset
```

### Least and largest elements in posets

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-least-element-Poset-Prop : element-Poset X → UU-Prop (l1 ⊔ l2)
  is-least-element-Poset-Prop =
    is-least-element-Preorder-Prop (preorder-Poset X)

  is-least-element-Poset : element-Poset X → UU (l1 ⊔ l2)
  is-least-element-Poset = is-least-element-Preorder (preorder-Poset X)

  is-prop-is-least-element-Poset :
    (x : element-Poset X) → is-prop (is-least-element-Poset x)
  is-prop-is-least-element-Poset =
    is-prop-is-least-element-Preorder (preorder-Poset X)

  least-element-Poset : UU (l1 ⊔ l2)
  least-element-Poset = least-element-Preorder (preorder-Poset X)

  all-elements-equal-least-element-Poset :
    all-elements-equal least-element-Poset
  all-elements-equal-least-element-Poset (pair x H) (pair y K) =
    eq-subtype
      ( is-prop-is-least-element-Poset)
      ( antisymmetric-leq-Poset X x y (H y) (K x))

  is-prop-least-element-Poset : is-prop least-element-Poset
  is-prop-least-element-Poset =
    is-prop-all-elements-equal all-elements-equal-least-element-Poset

  has-least-element-Poset-Prop : UU-Prop (l1 ⊔ l2)
  pr1 has-least-element-Poset-Prop = least-element-Poset
  pr2 has-least-element-Poset-Prop = is-prop-least-element-Poset

  is-largest-element-Poset-Prop : element-Poset X → UU-Prop (l1 ⊔ l2)
  is-largest-element-Poset-Prop =
    is-largest-element-Preorder-Prop (preorder-Poset X)

  is-largest-element-Poset : element-Poset X → UU (l1 ⊔ l2)
  is-largest-element-Poset = is-largest-element-Preorder (preorder-Poset X)

  is-prop-is-largest-element-Poset :
    (x : element-Poset X) → is-prop (is-largest-element-Poset x)
  is-prop-is-largest-element-Poset =
    is-prop-is-largest-element-Preorder (preorder-Poset X)

  largest-element-Poset : UU (l1 ⊔ l2)
  largest-element-Poset = largest-element-Preorder (preorder-Poset X)

  all-elements-equal-largest-element-Poset :
    all-elements-equal largest-element-Poset
  all-elements-equal-largest-element-Poset (pair x H) (pair y K) =
    eq-subtype
      ( is-prop-is-largest-element-Poset)
      ( antisymmetric-leq-Poset X x y (K x) (H y))

  is-prop-largest-element-Poset : is-prop largest-element-Poset
  is-prop-largest-element-Poset =
    is-prop-all-elements-equal all-elements-equal-largest-element-Poset

  has-largest-element-Poset-Prop : UU-Prop (l1 ⊔ l2)
  pr1 has-largest-element-Poset-Prop = largest-element-Poset
  pr2 has-largest-element-Poset-Prop = is-prop-largest-element-Poset

```
