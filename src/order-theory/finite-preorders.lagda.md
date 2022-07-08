# Finite preorders

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module order-theory.finite-preorders where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.decidable-equality using (has-decidable-equality)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop; is-decidable-prop;
    is-decidable-prop-type-decidable-Prop; is-decidable-type-decidable-Prop;
    is-prop-type-decidable-Prop)
open import foundation.decidable-types using (is-decidable-Prop; is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.mere-equivalences using (mere-equiv)
open import foundation.propositions using
  ( UU-Prop; prod-Prop; Π-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.sets using (is-set)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)

open import order-theory.decidable-subpreorders using
  ( element-decidable-sub-Preorder; eq-element-decidable-sub-Preorder;
    leq-decidable-sub-preorder-Prop; leq-decidable-sub-Preorder;
    is-prop-leq-decidable-sub-Preorder; refl-leq-decidable-sub-Preorder;
    transitive-leq-decidable-sub-Preorder)
open import order-theory.preorders using
  ( Preorder; element-Preorder; leq-preorder-Prop; leq-Preorder;
    is-prop-leq-Preorder; refl-leq-Preorder; transitive-leq-Preorder)

open import univalent-combinatorics.decidable-subtypes using
  ( is-finite-type-decidable-subtype)
open import univalent-combinatorics.equality-finite-types using
  ( is-set-is-finite; has-decidable-equality-is-finite)
open import univalent-combinatorics.finite-types using
  ( is-finite-Prop; is-finite; 𝔽; type-𝔽; is-finite-type-𝔽;
    number-of-elements-is-finite; mere-equiv-is-finite)
open import univalent-combinatorics.standard-finite-types using
  ( Fin)
```

## Finite preorders

We say that a preorder X is finite if X has finitely many elements and the ordering relation on X is decidable.

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-finite-preorder-Prop : UU-Prop (l1 ⊔ l2)
  is-finite-preorder-Prop =
    prod-Prop
      ( is-finite-Prop (element-Preorder X))
      ( Π-Prop
        ( element-Preorder X)
        ( λ x →
          Π-Prop
            ( element-Preorder X)
            ( λ y → is-decidable-Prop (leq-preorder-Prop X x y))))

  is-finite-Preorder : UU (l1 ⊔ l2)
  is-finite-Preorder = type-Prop is-finite-preorder-Prop

  is-prop-is-finite-Preorder : is-prop is-finite-Preorder
  is-prop-is-finite-Preorder = is-prop-type-Prop is-finite-preorder-Prop

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

  leq-finite-preorder-decidable-Prop :
    (x y : element-Finite-Preorder) → decidable-Prop l
  leq-finite-preorder-decidable-Prop = pr1 (pr2 X)

  leq-Finite-Preorder : (x y : element-Finite-Preorder) → UU l
  leq-Finite-Preorder x y =
    type-decidable-Prop (leq-finite-preorder-decidable-Prop x y)

  is-decidable-prop-leq-Finite-Preorder :
    (x y : element-Finite-Preorder) →
    is-decidable-prop (leq-Finite-Preorder x y)
  is-decidable-prop-leq-Finite-Preorder x y =
    is-decidable-prop-type-decidable-Prop
      ( leq-finite-preorder-decidable-Prop x y)

  is-decidable-leq-Finite-Preorder :
    (x y : element-Finite-Preorder) → is-decidable (leq-Finite-Preorder x y)
  is-decidable-leq-Finite-Preorder x y =
    is-decidable-type-decidable-Prop (leq-finite-preorder-decidable-Prop x y)

  is-prop-leq-Finite-Preorder :
    (x y : element-Finite-Preorder) → is-prop (leq-Finite-Preorder x y)
  is-prop-leq-Finite-Preorder x y =
    is-prop-type-decidable-Prop (leq-finite-preorder-decidable-Prop x y)

  leq-Finite-preorder-Prop :
    (x y : element-Finite-Preorder) → UU-Prop l
  pr1 (leq-Finite-preorder-Prop x y) = leq-Finite-Preorder x y
  pr2 (leq-Finite-preorder-Prop x y) = is-prop-leq-Finite-Preorder x y

  refl-leq-Finite-Preorder :
    (x : element-Finite-Preorder) → leq-Finite-Preorder x x
  refl-leq-Finite-Preorder = pr1 (pr2 (pr2 X))

  transitive-leq-Finite-Preorder :
    (x y z : element-Finite-Preorder) →
    leq-Finite-Preorder y z → leq-Finite-Preorder x y → leq-Finite-Preorder x z
  transitive-leq-Finite-Preorder = pr2 (pr2 (pr2 X))

  preorder-Finite-Preorder : Preorder lzero l
  pr1 preorder-Finite-Preorder = element-Finite-Preorder
  pr1 (pr2 preorder-Finite-Preorder) = leq-Finite-preorder-Prop
  pr1 (pr2 (pr2 preorder-Finite-Preorder)) = refl-leq-Finite-Preorder
  pr2 (pr2 (pr2 preorder-Finite-Preorder)) = transitive-leq-Finite-Preorder

  is-finite-preorder-Finite-Preorder :
    is-finite-Preorder preorder-Finite-Preorder
  pr1 is-finite-preorder-Finite-Preorder = is-finite-element-Finite-Preorder
  pr2 is-finite-preorder-Finite-Preorder = is-decidable-leq-Finite-Preorder
```

### Decidable sub-preorders of finite preorders

```agda

module _
  {l1 l2 : Level} (X : Finite-Preorder l1)
  (S : element-Finite-Preorder X → decidable-Prop l2)
  where

  element-finite-sub-Preorder : UU l2
  element-finite-sub-Preorder =
    element-decidable-sub-Preorder (preorder-Finite-Preorder X) S

  is-finite-element-finite-sub-Preorder : is-finite element-finite-sub-Preorder
  is-finite-element-finite-sub-Preorder =
    is-finite-type-decidable-subtype S (is-finite-element-Finite-Preorder X)

  eq-element-finite-sub-Preorder :
    (x y : element-finite-sub-Preorder) → Id (pr1 x) (pr1 y) → Id x y
  eq-element-finite-sub-Preorder =
    eq-element-decidable-sub-Preorder (preorder-Finite-Preorder X) S

  leq-finite-sub-Preorder-decidable-Prop :
    (x y : element-finite-sub-Preorder) → decidable-Prop l1
  leq-finite-sub-Preorder-decidable-Prop x y =
    leq-finite-preorder-decidable-Prop X (pr1 x) (pr1 y)

  leq-finite-sub-preorder-Prop :
    (x y : element-finite-sub-Preorder) → UU-Prop l1
  leq-finite-sub-preorder-Prop =
    leq-decidable-sub-preorder-Prop (preorder-Finite-Preorder X) S

  leq-finite-sub-Preorder : (x y : element-finite-sub-Preorder) → UU l1
  leq-finite-sub-Preorder =
    leq-decidable-sub-Preorder (preorder-Finite-Preorder X) S

  is-prop-leq-finite-sub-Preorder :
    (x y : element-finite-sub-Preorder) →
    is-prop (leq-finite-sub-Preorder x y)
  is-prop-leq-finite-sub-Preorder =
    is-prop-leq-decidable-sub-Preorder (preorder-Finite-Preorder X) S

  refl-leq-finite-sub-Preorder :
    (x : element-finite-sub-Preorder) → leq-finite-sub-Preorder x x
  refl-leq-finite-sub-Preorder =
    refl-leq-decidable-sub-Preorder (preorder-Finite-Preorder X) S

  transitive-leq-finite-sub-Preorder :
    (x y z : element-finite-sub-Preorder) →
    leq-finite-sub-Preorder y z → leq-finite-sub-Preorder x y →
    leq-finite-sub-Preorder x z
  transitive-leq-finite-sub-Preorder =
    transitive-leq-decidable-sub-Preorder (preorder-Finite-Preorder X) S

module _
  {l : Level} (X : Finite-Preorder l)
  (S : element-Finite-Preorder X → decidable-Prop lzero)
  where

  element-finite-sub-Preorder-𝔽 : 𝔽
  pr1 element-finite-sub-Preorder-𝔽 = element-finite-sub-Preorder X S
  pr2 element-finite-sub-Preorder-𝔽 = is-finite-element-finite-sub-Preorder X S
  
  finite-sub-Preorder : Finite-Preorder l
  pr1 finite-sub-Preorder = element-finite-sub-Preorder-𝔽
  pr1 (pr2 finite-sub-Preorder) = leq-finite-sub-Preorder-decidable-Prop X S
  pr1 (pr2 (pr2 finite-sub-Preorder)) = refl-leq-finite-sub-Preorder X S
  pr2 (pr2 (pr2 finite-sub-Preorder)) = transitive-leq-finite-sub-Preorder X S
```
