---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module order-theory.preorders where

open import univalent-foundations public
```

## Preorders

```agda
Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Preorder l1 l2 =
  Σ ( UU l1)
    ( λ X →
      Σ ( X → X → UU-Prop l2)
        ( λ R →
          ( (x : X) → type-Prop (R x x)) ×
          ( (x y z : X) →
            type-Prop (R y z) → type-Prop (R x y) → type-Prop (R x z))))

module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  element-Preorder : UU l1
  element-Preorder = pr1 X

  leq-Preorder-Prop : (x y : element-Preorder) → UU-Prop l2
  leq-Preorder-Prop = pr1 (pr2 X)

  leq-Preorder : (x y : element-Preorder) → UU l2
  leq-Preorder x y = type-Prop (leq-Preorder-Prop x y)

  is-prop-leq-Preorder : (x y : element-Preorder) → is-prop (leq-Preorder x y)
  is-prop-leq-Preorder x y = is-prop-type-Prop (leq-Preorder-Prop x y)

  refl-leq-Preorder : (x : element-Preorder) → leq-Preorder x x
  refl-leq-Preorder = pr1 (pr2 (pr2 X))

  transitive-leq-Preorder :
    (x y z : element-Preorder) →
    leq-Preorder y z → leq-Preorder x y → leq-Preorder x z
  transitive-leq-Preorder = pr2 (pr2 (pr2 X))

  incident-Preorder-Prop : (x y : element-Preorder) → UU-Prop l2
  incident-Preorder-Prop x y =
    disj-Prop (leq-Preorder-Prop x y) (leq-Preorder-Prop y x)

  incident-Preorder : (x y : element-Preorder) → UU l2
  incident-Preorder x y = type-Prop (incident-Preorder-Prop x y)

  is-prop-incident-Preorder :
    (x y : element-Preorder) → is-prop (incident-Preorder x y)
  is-prop-incident-Preorder x y = is-prop-type-Prop (incident-Preorder-Prop x y)

  is-total-Preorder-Prop : UU-Prop (l1 ⊔ l2)
  is-total-Preorder-Prop =
    Π-Prop element-Preorder
      ( λ x → Π-Prop element-Preorder (λ y → incident-Preorder-Prop x y))

  is-total-Preorder : UU (l1 ⊔ l2)
  is-total-Preorder = type-Prop is-total-Preorder-Prop

  is-prop-is-total-Preorder : is-prop is-total-Preorder
  is-prop-is-total-Preorder = is-prop-type-Prop is-total-Preorder-Prop
```

### Least and largest elements in preorders

```
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-least-element-Preorder-Prop : element-Preorder X → UU-Prop (l1 ⊔ l2)
  is-least-element-Preorder-Prop x =
    Π-Prop (element-Preorder X) (leq-Preorder-Prop X x)

  is-least-element-Preorder : element-Preorder X → UU (l1 ⊔ l2)
  is-least-element-Preorder x = type-Prop (is-least-element-Preorder-Prop x)

  is-prop-is-least-element-Preorder :
    (x : element-Preorder X) → is-prop (is-least-element-Preorder x)
  is-prop-is-least-element-Preorder x =
    is-prop-type-Prop (is-least-element-Preorder-Prop x)

  least-element-Preorder : UU (l1 ⊔ l2)
  least-element-Preorder = Σ (element-Preorder X) is-least-element-Preorder

  is-largest-element-Preorder-Prop : element-Preorder X → UU-Prop (l1 ⊔ l2)
  is-largest-element-Preorder-Prop x =
    Π-Prop (element-Preorder X) (λ y → leq-Preorder-Prop X y x)

  is-largest-element-Preorder : element-Preorder X → UU (l1 ⊔ l2)
  is-largest-element-Preorder x = type-Prop (is-largest-element-Preorder-Prop x)

  is-prop-is-largest-element-Preorder :
    (x : element-Preorder X) → is-prop (is-largest-element-Preorder x)
  is-prop-is-largest-element-Preorder x =
    is-prop-type-Prop (is-largest-element-Preorder-Prop x)

  largest-element-Preorder : UU (l1 ⊔ l2)
  largest-element-Preorder = Σ (element-Preorder X) is-largest-element-Preorder
```

### Finite preorders

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

### Sub-preorders

```agda

module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2) (S : element-Preorder X → UU-Prop l3)
  where

  element-sub-Preorder : UU (l1 ⊔ l3)
  element-sub-Preorder = total-subtype S

  eq-element-sub-Preorder :
    (x y : element-sub-Preorder) →
    Eq-total-subtype (λ z → is-prop-type-Prop (S z)) x y → Id x y
  eq-element-sub-Preorder x y = eq-subtype (λ x → is-prop-type-Prop (S x))

  leq-sub-Preorder-Prop : (x y : element-sub-Preorder) → UU-Prop l2
  leq-sub-Preorder-Prop x y = leq-Preorder-Prop X (pr1 x) (pr1 y)

  leq-sub-Preorder : (x y : element-sub-Preorder) → UU l2
  leq-sub-Preorder x y = type-Prop (leq-sub-Preorder-Prop x y)

  is-prop-leq-sub-Preorder :
    (x y : element-sub-Preorder) → is-prop (leq-sub-Preorder x y)
  is-prop-leq-sub-Preorder x y =
    is-prop-type-Prop (leq-sub-Preorder-Prop x y)

  refl-leq-sub-Preorder : (x : element-sub-Preorder) → leq-sub-Preorder x x
  refl-leq-sub-Preorder x = refl-leq-Preorder X (pr1 x)

  transitive-leq-sub-Preorder :
    (x y z : element-sub-Preorder) →
    leq-sub-Preorder y z → leq-sub-Preorder x y → leq-sub-Preorder x z
  transitive-leq-sub-Preorder x y z =
    transitive-leq-Preorder X (pr1 x) (pr1 y) (pr1 z)

  sub-Preorder : Preorder (l1 ⊔ l3) l2
  pr1 sub-Preorder = element-sub-Preorder
  pr1 (pr2 sub-Preorder) = leq-sub-Preorder-Prop
  pr1 (pr2 (pr2 sub-Preorder)) = refl-leq-sub-Preorder
  pr2 (pr2 (pr2 sub-Preorder)) = transitive-leq-sub-Preorder
```

### Inclusion of sub-preorders

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  module _
    {l3 l4 : Level} (S : element-Preorder X → UU-Prop l3)
    (T : element-Preorder X → UU-Prop l4)
    where
    
    inclusion-sub-Preorder-Prop : UU-Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-sub-Preorder-Prop =
      Π-Prop (element-Preorder X) (λ x → hom-Prop (S x) (T x))

    inclusion-sub-Preorder : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-sub-Preorder = type-Prop inclusion-sub-Preorder-Prop

    is-prop-inclusion-sub-Preorder : is-prop inclusion-sub-Preorder
    is-prop-inclusion-sub-Preorder =
      is-prop-type-Prop inclusion-sub-Preorder-Prop

  refl-inclusion-sub-Preorder :
    {l3 : Level} (S : element-Preorder X → UU-Prop l3) →
    inclusion-sub-Preorder S S
  refl-inclusion-sub-Preorder S x = id

  transitive-inclusion-sub-Preorder :
    {l3 l4 l5 : Level} (S : element-Preorder X → UU-Prop l3)
    (T : element-Preorder X → UU-Prop l4)
    (U : element-Preorder X → UU-Prop l5) →
    inclusion-sub-Preorder T U → inclusion-sub-Preorder S T →
    inclusion-sub-Preorder S U
  transitive-inclusion-sub-Preorder S T U g f x = (g x) ∘ (f x)

  Sub-Preorder : (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (Sub-Preorder l) = element-Preorder X → UU-Prop l
  pr1 (pr2 (Sub-Preorder l)) = inclusion-sub-Preorder-Prop
  pr1 (pr2 (pr2 (Sub-Preorder l))) = refl-inclusion-sub-Preorder
  pr2 (pr2 (pr2 (Sub-Preorder l))) = transitive-inclusion-sub-Preorder

```

### Chains in preorders

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-chain-sub-Preorder-Prop :
    {l3 : Level} (S : element-Preorder X → UU-Prop l3) → UU-Prop (l1 ⊔ l2 ⊔ l3)
  is-chain-sub-Preorder-Prop S = is-total-Preorder-Prop (sub-Preorder X S)

  is-chain-sub-Preorder :
    {l3 : Level} (S : element-Preorder X → UU-Prop l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-chain-sub-Preorder S = type-Prop (is-chain-sub-Preorder-Prop S)

  is-prop-is-chain-sub-Preorder :
    {l3 : Level} (S : element-Preorder X → UU-Prop l3) →
    is-prop (is-chain-sub-Preorder S)
  is-prop-is-chain-sub-Preorder S =
    is-prop-type-Prop (is-chain-sub-Preorder-Prop S)

chain-Preorder :
  {l1 l2 : Level} (l : Level) (X : Preorder l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l)
chain-Preorder l X =
  Σ (element-Preorder X → UU-Prop l) (is-chain-sub-Preorder X)
```
