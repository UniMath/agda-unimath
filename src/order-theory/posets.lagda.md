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

## Subposets

```agda

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (S : element-Poset X → UU-Prop l3)
  where

  element-sub-Poset : UU (l1 ⊔ l3)
  element-sub-Poset = element-sub-Preorder (preorder-Poset X) S

  eq-element-sub-Poset :
    (x y : element-sub-Poset) →
    Eq-total-subtype (λ z → is-prop-type-Prop (S z)) x y → Id x y
  eq-element-sub-Poset = eq-element-sub-Preorder (preorder-Poset X) S

  leq-sub-Poset-Prop : (x y : element-sub-Poset) → UU-Prop l2
  leq-sub-Poset-Prop = leq-sub-Preorder-Prop (preorder-Poset X) S

  leq-sub-Poset : (x y : element-sub-Poset) → UU l2
  leq-sub-Poset = leq-sub-Preorder (preorder-Poset X) S

  is-prop-leq-sub-Poset :
    (x y : element-sub-Poset) → is-prop (leq-sub-Poset x y)
  is-prop-leq-sub-Poset = is-prop-leq-sub-Preorder (preorder-Poset X) S

  refl-leq-sub-Poset : (x : element-sub-Poset) → leq-sub-Poset x x
  refl-leq-sub-Poset = refl-leq-sub-Preorder (preorder-Poset X) S

  transitive-leq-sub-Poset :
    (x y z : element-sub-Poset) →
    leq-sub-Poset y z → leq-sub-Poset x y → leq-sub-Poset x z
  transitive-leq-sub-Poset = transitive-leq-sub-Preorder (preorder-Poset X) S

  antisymmetric-leq-sub-Poset :
    (x y : element-sub-Poset) → leq-sub-Poset x y → leq-sub-Poset y x → Id x y
  antisymmetric-leq-sub-Poset x y H K =
    eq-element-sub-Poset x y (antisymmetric-leq-Poset X (pr1 x) (pr1 y) H K)

  sub-Poset : Poset (l1 ⊔ l3) l2
  pr1 sub-Poset = element-sub-Poset
  pr1 (pr2 sub-Poset) = leq-sub-Poset-Prop
  pr1 (pr1 (pr2 (pr2 sub-Poset))) = refl-leq-sub-Poset
  pr2 (pr1 (pr2 (pr2 sub-Poset))) = transitive-leq-sub-Poset
  pr2 (pr2 (pr2 sub-Poset)) = antisymmetric-leq-sub-Poset
  
```

### Decidable sub-posets

```agda

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2)
  (S : element-Poset X → decidable-Prop l3)
  where

  element-decidable-sub-Poset : UU (l1 ⊔ l3)
  element-decidable-sub-Poset =
    element-sub-Poset X (subtype-decidable-subtype S)

  eq-element-decidable-sub-Poset :
    (x y : element-decidable-sub-Poset) →
    Eq-total-subtype (λ z → is-prop-type-decidable-Prop (S z)) x y → Id x y
  eq-element-decidable-sub-Poset =
    eq-element-sub-Poset X (subtype-decidable-subtype S)

  leq-decidable-sub-Poset-Prop :
    (x y : element-decidable-sub-Poset) → UU-Prop l2
  leq-decidable-sub-Poset-Prop =
    leq-sub-Poset-Prop X (subtype-decidable-subtype S)

  leq-decidable-sub-Poset : (x y : element-decidable-sub-Poset) → UU l2
  leq-decidable-sub-Poset =
    leq-sub-Poset X (subtype-decidable-subtype S)

  is-prop-leq-decidable-sub-Poset :
    (x y : element-decidable-sub-Poset) →
    is-prop (leq-decidable-sub-Poset x y)
  is-prop-leq-decidable-sub-Poset =
    is-prop-leq-sub-Poset X (subtype-decidable-subtype S)

  refl-leq-decidable-sub-Poset :
    (x : element-decidable-sub-Poset) → leq-decidable-sub-Poset x x
  refl-leq-decidable-sub-Poset =
    refl-leq-sub-Poset X (subtype-decidable-subtype S)

  transitive-leq-decidable-sub-Poset :
    (x y z : element-decidable-sub-Poset) →
    leq-decidable-sub-Poset y z → leq-decidable-sub-Poset x y →
    leq-decidable-sub-Poset x z
  transitive-leq-decidable-sub-Poset =
    transitive-leq-sub-Poset X (subtype-decidable-subtype S)

  decidable-sub-Poset : Poset (l1 ⊔ l3) l2
  decidable-sub-Poset = sub-Poset X (subtype-decidable-subtype S)
```

### Inclusion of sub-posets

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  module _
    {l3 l4 : Level} (S : element-Poset X → UU-Prop l3)
    (T : element-Poset X → UU-Prop l4)
    where
    
    inclusion-sub-Poset-Prop : UU-Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-sub-Poset-Prop =
      inclusion-sub-Preorder-Prop (preorder-Poset X) S T

    inclusion-sub-Poset : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-sub-Poset = inclusion-sub-Preorder (preorder-Poset X) S T

    is-prop-inclusion-sub-Poset : is-prop inclusion-sub-Poset
    is-prop-inclusion-sub-Poset =
      is-prop-inclusion-sub-Preorder (preorder-Poset X) S T

  refl-inclusion-sub-Poset :
    {l3 : Level} (S : element-Poset X → UU-Prop l3) →
    inclusion-sub-Poset S S
  refl-inclusion-sub-Poset = refl-inclusion-sub-Preorder (preorder-Poset X)

  transitive-inclusion-sub-Poset :
    {l3 l4 l5 : Level} (S : element-Poset X → UU-Prop l3)
    (T : element-Poset X → UU-Prop l4)
    (U : element-Poset X → UU-Prop l5) →
    inclusion-sub-Poset T U → inclusion-sub-Poset S T →
    inclusion-sub-Poset S U
  transitive-inclusion-sub-Poset =
    transitive-inclusion-sub-Preorder (preorder-Poset X) 

  sub-poset-Preorder : (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (sub-poset-Preorder l) = element-Poset X → UU-Prop l
  pr1 (pr2 (sub-poset-Preorder l)) = inclusion-sub-Poset-Prop
  pr1 (pr2 (pr2 (sub-poset-Preorder l))) = refl-inclusion-sub-Poset
  pr2 (pr2 (pr2 (sub-poset-Preorder l))) = transitive-inclusion-sub-Poset

```

### Chains in preorders

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-chain-sub-Poset-Prop :
    {l3 : Level} (S : element-Poset X → UU-Prop l3) → UU-Prop (l1 ⊔ l2 ⊔ l3)
  is-chain-sub-Poset-Prop = is-chain-sub-Preorder-Prop (preorder-Poset X)

  is-chain-sub-Poset :
    {l3 : Level} (S : element-Poset X → UU-Prop l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-chain-sub-Poset = is-chain-sub-Preorder (preorder-Poset X)

  is-prop-is-chain-sub-Poset :
    {l3 : Level} (S : element-Poset X → UU-Prop l3) →
    is-prop (is-chain-sub-Poset S)
  is-prop-is-chain-sub-Poset = is-prop-is-chain-sub-Preorder (preorder-Poset X)

chain-Poset :
  {l1 l2 : Level} (l : Level) (X : Poset l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l)
chain-Poset l X = chain-Preorder l (preorder-Poset X)

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (C : chain-Poset l3 X)
  where

  sub-preorder-chain-Poset : element-Poset X → UU-Prop l3
  sub-preorder-chain-Poset =
    sub-preorder-chain-Preorder (preorder-Poset X) C

  element-chain-Poset : UU (l1 ⊔ l3)
  element-chain-Poset = element-chain-Preorder (preorder-Poset X) C

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where
  
  inclusion-chain-Poset-Prop :
    {l3 l4 : Level} → chain-Poset l3 X → chain-Poset l4 X →
    UU-Prop (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Poset-Prop = inclusion-chain-Preorder-Prop (preorder-Poset X)

  inclusion-chain-Poset :
    {l3 l4 : Level} → chain-Poset l3 X → chain-Poset l4 X → UU (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Poset = inclusion-chain-Preorder (preorder-Poset X)

  is-prop-inclusion-chain-Poset :
    {l3 l4 : Level} (C : chain-Poset l3 X) (D : chain-Poset l4 X) →
    is-prop (inclusion-chain-Poset C D)
  is-prop-inclusion-chain-Poset =
    is-prop-inclusion-chain-Preorder (preorder-Poset X)
```

### Maximal chains in preorders

```agda

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where
  
  is-maximal-chain-Poset-Prop :
    {l3 : Level} → chain-Poset l3 X → UU-Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-Poset-Prop =
    is-maximal-chain-Preorder-Prop (preorder-Poset X)

  is-maximal-chain-Poset :
    {l3 : Level} → chain-Poset l3 X → UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-Poset = is-maximal-chain-Preorder (preorder-Poset X)

  is-prop-is-maximal-chain-Poset :
    {l3 : Level} (C : chain-Poset l3 X) → is-prop (is-maximal-chain-Poset C)
  is-prop-is-maximal-chain-Poset =
    is-prop-is-maximal-chain-Preorder (preorder-Poset X)

maximal-chain-Poset :
  {l1 l2 : Level} (l3 : Level) (X : Poset l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
maximal-chain-Poset l3 X = maximal-chain-Preorder l3 (preorder-Poset X)

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (C : maximal-chain-Poset l3 X)
  where

  chain-maximal-chain-Poset : chain-Poset l3 X
  chain-maximal-chain-Poset = chain-maximal-chain-Preorder (preorder-Poset X) C

  is-maximal-chain-maximal-chain-Poset :
    is-maximal-chain-Poset X chain-maximal-chain-Poset
  is-maximal-chain-maximal-chain-Poset =
    is-maximal-chain-maximal-chain-Preorder (preorder-Poset X) C

  element-maximal-chain-Poset : UU (l1 ⊔ l3)
  element-maximal-chain-Poset =
    element-maximal-chain-Preorder (preorder-Poset X) C
