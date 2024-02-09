# Large binary relations

```agda
module foundation.large-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.reflexive-relations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.propositions
```

</details>

## Idea

A **large binary relation** on a family of types indexed by universe levels `A`
is a family of types `R x y` depending on two variables `x : A l1` and
`y : A l2`. In the special case where each `R x y` is a
[proposition](foundation-core.propositions.md), we say that the relation is
valued in propositions. Thus, we take a general relation to mean a
_proof-relevant_ relation.

## Definition

### Large relations valued in types

```agda
Large-Relation :
  (α : Level → Level) (β : Level → Level → Level)
  (A : (l : Level) → UU (α l)) → UUω
Large-Relation α β A = {l1 l2 : Level} → A l1 → A l2 → UU (β l1 l2)

total-space-Large-Relation :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) → Large-Relation α β A → UUω
total-space-Large-Relation A R =
  (l1 l2 : Level) → Σ (A l1 × A l2) (λ (a , a') → R a a')
```

### Large relations valued in propositions

```agda
is-prop-Large-Relation :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) → Large-Relation α β A → UUω
is-prop-Large-Relation A R =
  {l1 l2 : Level} (x : A l1) (y : A l2) → is-prop (R x y)

Large-Relation-Prop :
  (α : Level → Level) (β : Level → Level → Level)
  (A : (l : Level) → UU (α l)) →
  UUω
Large-Relation-Prop α β A = {l1 l2 : Level} → A l1 → A l2 → Prop (β l1 l2)

type-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) →
  Large-Relation-Prop α β A → Large-Relation α β A
type-Large-Relation-Prop A R x y = pr1 (R x y)

is-prop-type-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop α β A) →
  is-prop-Large-Relation A (type-Large-Relation-Prop A R)
is-prop-type-Large-Relation-Prop A R x y = pr2 (R x y)

total-space-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop α β A) →
  UUω
total-space-Large-Relation-Prop A R =
  (l1 l2 : Level) →
  Σ (A l1 × A l2) (λ (a , a') → type-Large-Relation-Prop A R a a')
```

## Small relations from large relations

```agda
relation-Large-Relation :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) (R : Large-Relation α β A)
  (l : Level) → Relation (β l l) (A l)
relation-Large-Relation A R l x y = R x y

relation-prop-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) (R : Large-Relation-Prop α β A)
  (l : Level) → Relation-Prop (β l l) (A l)
relation-prop-Large-Relation-Prop A R l x y = R x y

relation-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) (R : Large-Relation-Prop α β A)
  (l : Level) → Relation (β l l) (A l)
relation-Large-Relation-Prop A R =
  relation-Large-Relation A (type-Large-Relation-Prop A R)
```

## Specifications of properties of binary relations

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation α β A)
  where

  is-reflexive-Large-Relation : UUω
  is-reflexive-Large-Relation =
    {l : Level} → is-reflexive (relation-Large-Relation A R l)

  is-symmetric-Large-Relation : UUω
  is-symmetric-Large-Relation =
    {l1 l2 : Level} (x : A l1) (y : A l2) → R x y → R y x

  is-transitive-Large-Relation : UUω
  is-transitive-Large-Relation =
    {l1 l2 l3 : Level} (x : A l1) (y : A l2) (z : A l3) → R y z → R x y → R x z

  is-antisymmetric-Large-Relation : UUω
  is-antisymmetric-Large-Relation =
    {l : Level} → is-antisymmetric (relation-Large-Relation A R l)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop α β A)
  where

  is-reflexive-Large-Relation-Prop : UUω
  is-reflexive-Large-Relation-Prop =
    is-reflexive-Large-Relation A (type-Large-Relation-Prop A R)

  is-large-symmetric-Large-Relation-Prop : UUω
  is-large-symmetric-Large-Relation-Prop =
    is-symmetric-Large-Relation A (type-Large-Relation-Prop A R)

  is-transitive-Large-Relation-Prop : UUω
  is-transitive-Large-Relation-Prop =
    is-transitive-Large-Relation A (type-Large-Relation-Prop A R)

  is-antisymmetric-Large-Relation-Prop : UUω
  is-antisymmetric-Large-Relation-Prop =
    is-antisymmetric-Large-Relation A (type-Large-Relation-Prop A R)
```

## See also

- [(Small) binary relations](foundation.binary-relations.md)
- [Large preorders](order-theory.large-preorders.md)
- [Large posets](order-theory.large-posets.md)
