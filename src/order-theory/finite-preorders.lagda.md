# Finite preorders

```agda
module order-theory.finite-preorders where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.decidable-preorders
open import order-theory.decidable-subpreorders
open import order-theory.preorders

open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We say that a [preorder](order-theory.preorders.md) `P` is **finite** if `P` has
[finitely many elements](univalent-combinatorics.finite-types.md) and the
ordering relation on `P` is [decidable](foundation.decidable-relations.md).

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-finite-Preorder-Prop : Prop (l1 ⊔ l2)
  is-finite-Preorder-Prop =
    product-Prop
      ( is-finite-Prop (type-Preorder P))
      ( is-decidable-leq-prop-Preorder P)

  is-finite-Preorder : UU (l1 ⊔ l2)
  is-finite-Preorder = type-Prop is-finite-Preorder-Prop

  is-prop-is-finite-Preorder : is-prop is-finite-Preorder
  is-prop-is-finite-Preorder = is-prop-type-Prop is-finite-Preorder-Prop

  is-finite-type-is-finite-Preorder :
    is-finite-Preorder → is-finite (type-Preorder P)
  is-finite-type-is-finite-Preorder = pr1

  is-decidable-leq-is-finite-Preorder :
    is-finite-Preorder →
    (x y : type-Preorder P) → is-decidable (leq-Preorder P x y)
  is-decidable-leq-is-finite-Preorder H = pr2 H

Finite-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Finite-Preorder l1 l2 =
  Σ ( Finite-Type l1)
    ( λ P →
      Σ ( (x y : type-Finite-Type P) → Decidable-Prop l2)
        ( λ R →
          ( (x : type-Finite-Type P) → type-Decidable-Prop (R x x)) ×
          ( (x y z : type-Finite-Type P) →
            type-Decidable-Prop (R y z) → type-Decidable-Prop (R x y) →
            type-Decidable-Prop (R x z))))

finite-preorder-is-finite-Preorder :
  {l1 l2 : Level} (P : Preorder l1 l2) → is-finite-Preorder P →
  Finite-Preorder l1 l2
pr1 (pr1 (finite-preorder-is-finite-Preorder P H)) = type-Preorder P
pr2 (pr1 (finite-preorder-is-finite-Preorder P H)) = pr1 H
pr1 (pr1 (pr2 (finite-preorder-is-finite-Preorder P H)) x y) =
  leq-Preorder P x y
pr1 (pr2 (pr1 (pr2 (finite-preorder-is-finite-Preorder P H)) x y)) =
  is-prop-leq-Preorder P x y
pr2 (pr2 (pr1 (pr2 (finite-preorder-is-finite-Preorder P H)) x y)) =
  pr2 H x y
pr1 (pr2 (pr2 (finite-preorder-is-finite-Preorder P H))) =
  refl-leq-Preorder P
pr2 (pr2 (pr2 (finite-preorder-is-finite-Preorder P H))) =
  transitive-leq-Preorder P

module _
  {l1 l2 : Level} (P : Finite-Preorder l1 l2)
  where

  finite-type-Finite-Preorder : Finite-Type l1
  finite-type-Finite-Preorder = pr1 P

  type-Finite-Preorder : UU l1
  type-Finite-Preorder = type-Finite-Type finite-type-Finite-Preorder

  is-finite-type-Finite-Preorder : is-finite type-Finite-Preorder
  is-finite-type-Finite-Preorder =
    is-finite-type-Finite-Type finite-type-Finite-Preorder

  number-of-types-Finite-Preorder : ℕ
  number-of-types-Finite-Preorder =
    number-of-elements-is-finite is-finite-type-Finite-Preorder

  mere-equiv-type-Finite-Preorder :
    mere-equiv (Fin number-of-types-Finite-Preorder) type-Finite-Preorder
  mere-equiv-type-Finite-Preorder =
    mere-equiv-is-finite is-finite-type-Finite-Preorder

  is-set-type-Finite-Preorder : is-set type-Finite-Preorder
  is-set-type-Finite-Preorder =
    is-set-is-finite is-finite-type-Finite-Preorder

  has-decidable-equality-type-Finite-Preorder :
    has-decidable-equality type-Finite-Preorder
  has-decidable-equality-type-Finite-Preorder =
    has-decidable-equality-is-finite is-finite-type-Finite-Preorder

  leq-finite-preorder-Decidable-Prop :
    (x y : type-Finite-Preorder) → Decidable-Prop l2
  leq-finite-preorder-Decidable-Prop = pr1 (pr2 P)

  leq-Finite-Preorder : (x y : type-Finite-Preorder) → UU l2
  leq-Finite-Preorder x y =
    type-Decidable-Prop (leq-finite-preorder-Decidable-Prop x y)

  is-decidable-prop-leq-Finite-Preorder :
    (x y : type-Finite-Preorder) →
    is-decidable-prop (leq-Finite-Preorder x y)
  is-decidable-prop-leq-Finite-Preorder x y =
    is-decidable-prop-type-Decidable-Prop
      ( leq-finite-preorder-Decidable-Prop x y)

  is-decidable-leq-Finite-Preorder :
    (x y : type-Finite-Preorder) → is-decidable (leq-Finite-Preorder x y)
  is-decidable-leq-Finite-Preorder x y =
    is-decidable-Decidable-Prop (leq-finite-preorder-Decidable-Prop x y)

  is-prop-leq-Finite-Preorder :
    (x y : type-Finite-Preorder) → is-prop (leq-Finite-Preorder x y)
  is-prop-leq-Finite-Preorder x y =
    is-prop-type-Decidable-Prop (leq-finite-preorder-Decidable-Prop x y)

  leq-Finite-Preorder-Prop :
    (x y : type-Finite-Preorder) → Prop l2
  pr1 (leq-Finite-Preorder-Prop x y) = leq-Finite-Preorder x y
  pr2 (leq-Finite-Preorder-Prop x y) = is-prop-leq-Finite-Preorder x y

  refl-leq-Finite-Preorder :
    (x : type-Finite-Preorder) → leq-Finite-Preorder x x
  refl-leq-Finite-Preorder = pr1 (pr2 (pr2 P))

  transitive-leq-Finite-Preorder : is-transitive leq-Finite-Preorder
  transitive-leq-Finite-Preorder = pr2 (pr2 (pr2 P))

  preorder-Finite-Preorder : Preorder l1 l2
  pr1 preorder-Finite-Preorder = type-Finite-Preorder
  pr1 (pr2 preorder-Finite-Preorder) = leq-Finite-Preorder-Prop
  pr1 (pr2 (pr2 preorder-Finite-Preorder)) = refl-leq-Finite-Preorder
  pr2 (pr2 (pr2 preorder-Finite-Preorder)) = transitive-leq-Finite-Preorder

  is-finite-preorder-Finite-Preorder :
    is-finite-Preorder preorder-Finite-Preorder
  pr1 is-finite-preorder-Finite-Preorder = is-finite-type-Finite-Preorder
  pr2 is-finite-preorder-Finite-Preorder = is-decidable-leq-Finite-Preorder
```

### Decidable subpreorders of finite preorders

```agda
module _
  {l1 l2 l3 : Level} (P : Finite-Preorder l1 l2)
  (S : type-Finite-Preorder P → Decidable-Prop l3)
  where

  type-finite-Subpreorder : UU (l1 ⊔ l3)
  type-finite-Subpreorder =
    type-Decidable-Subpreorder (preorder-Finite-Preorder P) S

  is-finite-type-finite-Subpreorder : is-finite type-finite-Subpreorder
  is-finite-type-finite-Subpreorder =
    is-finite-type-decidable-subtype S (is-finite-type-Finite-Preorder P)

  eq-type-finite-Subpreorder :
    (x y : type-finite-Subpreorder) → Id (pr1 x) (pr1 y) → x ＝ y
  eq-type-finite-Subpreorder =
    eq-type-Decidable-Subpreorder (preorder-Finite-Preorder P) S

  leq-finite-Subpreorder-Decidable-Prop :
    (x y : type-finite-Subpreorder) → Decidable-Prop l2
  leq-finite-Subpreorder-Decidable-Prop x y =
    leq-finite-preorder-Decidable-Prop P (pr1 x) (pr1 y)

  leq-finite-Subpreorder-Prop :
    (x y : type-finite-Subpreorder) → Prop l2
  leq-finite-Subpreorder-Prop =
    leq-Decidable-Subpreorder-Prop (preorder-Finite-Preorder P) S

  leq-finite-Subpreorder : (x y : type-finite-Subpreorder) → UU l2
  leq-finite-Subpreorder =
    leq-Decidable-Subpreorder (preorder-Finite-Preorder P) S

  is-prop-leq-finite-Subpreorder :
    (x y : type-finite-Subpreorder) →
    is-prop (leq-finite-Subpreorder x y)
  is-prop-leq-finite-Subpreorder =
    is-prop-leq-Decidable-Subpreorder (preorder-Finite-Preorder P) S

  refl-leq-finite-Subpreorder :
    (x : type-finite-Subpreorder) → leq-finite-Subpreorder x x
  refl-leq-finite-Subpreorder =
    refl-leq-Decidable-Subpreorder (preorder-Finite-Preorder P) S

  transitive-leq-finite-Subpreorder : is-transitive leq-finite-Subpreorder
  transitive-leq-finite-Subpreorder =
    transitive-leq-Decidable-Subpreorder (preorder-Finite-Preorder P) S

module _
  {l1 l2 l3 : Level} (P : Finite-Preorder l1 l2)
  (S : type-Finite-Preorder P → Decidable-Prop l3)
  where

  type-finite-Subpreorder-Finite-Preorder : Finite-Type (l1 ⊔ l3)
  pr1 type-finite-Subpreorder-Finite-Preorder = type-finite-Subpreorder P S
  pr2 type-finite-Subpreorder-Finite-Preorder =
    is-finite-type-finite-Subpreorder P S

  finite-Subpreorder : Finite-Preorder (l1 ⊔ l3) l2
  pr1 finite-Subpreorder = type-finite-Subpreorder-Finite-Preorder
  pr1 (pr2 finite-Subpreorder) = leq-finite-Subpreorder-Decidable-Prop P S
  pr1 (pr2 (pr2 finite-Subpreorder)) = refl-leq-finite-Subpreorder P S
  pr2 (pr2 (pr2 finite-Subpreorder)) = transitive-leq-finite-Subpreorder P S
```
