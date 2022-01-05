---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module order-theory.finite-preorders where

open import order-theory.preorders public
```

## Finite preorders

We say that a preorder X is finite if X has finitely many elements and the ordering relation on X is decidable.

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-finite-Preorder-Prop : UU-Prop (l1 ⊔ l2)
  is-finite-Preorder-Prop =
    prod-Prop
      ( is-finite-Prop (element-Preorder X))
      ( Π-Prop
        ( element-Preorder X)
        ( λ x →
          Π-Prop
            ( element-Preorder X)
            ( λ y → is-decidable-Prop (leq-Preorder-Prop X x y))))

  is-finite-Preorder : UU (l1 ⊔ l2)
  is-finite-Preorder = type-Prop is-finite-Preorder-Prop

  is-prop-is-finite-Preorder : is-prop is-finite-Preorder
  is-prop-is-finite-Preorder = is-prop-type-Prop is-finite-Preorder-Prop

  is-finite-element-is-finite-Preorder :
    is-finite-Preorder → is-finite (element-Preorder X)
  is-finite-element-is-finite-Preorder = pr1

  is-decidable-leq-is-finite-Preorder :
    is-finite-Preorder →
    (x y : element-Preorder X) → is-decidable (leq-Preorder X x y)
  is-decidable-leq-is-finite-Preorder H = pr2 H

Finite-Preorder : (l : Level) → UU (lsuc l)
Finite-Preorder l =
  Σ ( 𝔽)
    ( λ X →
      Σ ( (x y : type-𝔽 X) → decidable-Prop l)
        ( λ R →
          ( (x : type-𝔽 X) → type-decidable-Prop (R x x)) ×
          ( (x y z : type-𝔽 X) →
            type-decidable-Prop (R y z) → type-decidable-Prop (R x y) →
            type-decidable-Prop (R x z))))

finite-preorder-is-finite-Preorder :
  {l : Level} (X : Preorder lzero l) → is-finite-Preorder X → Finite-Preorder l
pr1 (pr1 (finite-preorder-is-finite-Preorder X H)) = element-Preorder X
pr2 (pr1 (finite-preorder-is-finite-Preorder X H)) = pr1 H
pr1 (pr1 (pr2 (finite-preorder-is-finite-Preorder X H)) x y) =
  leq-Preorder X x y
pr1 (pr2 (pr1 (pr2 (finite-preorder-is-finite-Preorder X H)) x y)) =
  is-prop-leq-Preorder X x y
pr2 (pr2 (pr1 (pr2 (finite-preorder-is-finite-Preorder X H)) x y)) =
  pr2 H x y
pr1 (pr2 (pr2 (finite-preorder-is-finite-Preorder X H))) =
  refl-leq-Preorder X
pr2 (pr2 (pr2 (finite-preorder-is-finite-Preorder X H))) =
  transitive-leq-Preorder X

module _
  {l : Level} (X : Finite-Preorder l)
  where

  element-Finite-Preorder-𝔽 : 𝔽
  element-Finite-Preorder-𝔽 = pr1 X

  element-Finite-Preorder : UU lzero
  element-Finite-Preorder = type-𝔽 element-Finite-Preorder-𝔽

  is-finite-element-Finite-Preorder : is-finite element-Finite-Preorder
  is-finite-element-Finite-Preorder =
    is-finite-type-𝔽 element-Finite-Preorder-𝔽

  number-of-elements-Finite-Preorder : ℕ
  number-of-elements-Finite-Preorder =
    number-of-elements-is-finite is-finite-element-Finite-Preorder

  mere-equiv-element-Finite-Preorder :
    mere-equiv (Fin number-of-elements-Finite-Preorder) element-Finite-Preorder
  mere-equiv-element-Finite-Preorder =
    mere-equiv-is-finite is-finite-element-Finite-Preorder

  is-set-element-Finite-Preorder : is-set element-Finite-Preorder
  is-set-element-Finite-Preorder =
    is-set-is-finite is-finite-element-Finite-Preorder

  has-decidable-equality-element-Finite-Preorder :
    has-decidable-equality element-Finite-Preorder
  has-decidable-equality-element-Finite-Preorder =
    has-decidable-equality-is-finite is-finite-element-Finite-Preorder

  leq-Finite-Preorder-decidable-Prop :
    (x y : element-Finite-Preorder) → decidable-Prop l
  leq-Finite-Preorder-decidable-Prop = pr1 (pr2 X)

  leq-Finite-Preorder : (x y : element-Finite-Preorder) → UU l
  leq-Finite-Preorder x y =
    type-decidable-Prop (leq-Finite-Preorder-decidable-Prop x y)

  is-decidable-prop-leq-Finite-Preorder :
    (x y : element-Finite-Preorder) →
    is-decidable-prop (leq-Finite-Preorder x y)
  is-decidable-prop-leq-Finite-Preorder x y =
    is-decidable-prop-type-decidable-Prop
      ( leq-Finite-Preorder-decidable-Prop x y)

  is-decidable-leq-Finite-Preorder :
    (x y : element-Finite-Preorder) → is-decidable (leq-Finite-Preorder x y)
  is-decidable-leq-Finite-Preorder x y =
    is-decidable-type-decidable-Prop (leq-Finite-Preorder-decidable-Prop x y)

  is-prop-leq-Finite-Preorder :
    (x y : element-Finite-Preorder) → is-prop (leq-Finite-Preorder x y)
  is-prop-leq-Finite-Preorder x y =
    is-prop-type-decidable-Prop (leq-Finite-Preorder-decidable-Prop x y)

  leq-Finite-Preorder-Prop :
    (x y : element-Finite-Preorder) → UU-Prop l
  pr1 (leq-Finite-Preorder-Prop x y) = leq-Finite-Preorder x y
  pr2 (leq-Finite-Preorder-Prop x y) = is-prop-leq-Finite-Preorder x y

  refl-leq-Finite-Preorder :
    (x : element-Finite-Preorder) → leq-Finite-Preorder x x
  refl-leq-Finite-Preorder = pr1 (pr2 (pr2 X))

  transitive-leq-Finite-Preorder :
    (x y z : element-Finite-Preorder) →
    leq-Finite-Preorder y z → leq-Finite-Preorder x y → leq-Finite-Preorder x z
  transitive-leq-Finite-Preorder = pr2 (pr2 (pr2 X))

  preorder-Finite-Preorder : Preorder lzero l
  pr1 preorder-Finite-Preorder = element-Finite-Preorder
  pr1 (pr2 preorder-Finite-Preorder) = leq-Finite-Preorder-Prop
  pr1 (pr2 (pr2 preorder-Finite-Preorder)) = refl-leq-Finite-Preorder
  pr2 (pr2 (pr2 preorder-Finite-Preorder)) = transitive-leq-Finite-Preorder

  is-finite-preorder-Finite-Preorder :
    is-finite-Preorder preorder-Finite-Preorder
  pr1 is-finite-preorder-Finite-Preorder = is-finite-element-Finite-Preorder
  pr2 is-finite-preorder-Finite-Preorder = is-decidable-leq-Finite-Preorder
```

