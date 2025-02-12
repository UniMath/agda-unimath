# Large binary relations

```agda
module foundation.large-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

A
{{#concept "large binary relation" Disambiguation="valued in types" Agda=Large-Relation}}
on a family of types indexed by universe levels `A` is a family of types `R x y`
depending on two variables `x : A l1` and `y : A l2`. In the special case where
each `R x y` is a [proposition](foundation-core.propositions.md), we say that
the relation is valued in propositions. Thus, we take a general relation to mean
a _proof-relevant_ relation.

## Definition

### Large relations valued in types

```agda
module _
  {α : Level → Level} (β : Level → Level → Level)
  (A : (l : Level) → UU (α l))
  where

  Large-Relation : UUω
  Large-Relation = {l1 l2 : Level} → A l1 → A l2 → UU (β l1 l2)

  total-space-Large-Relation : Large-Relation → UUω
  total-space-Large-Relation R =
    (l1 l2 : Level) → Σ (A l1 × A l2) (λ (a , a') → R a a')
```

### Large relations valued in propositions

```agda
is-prop-Large-Relation :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) → Large-Relation β A → UUω
is-prop-Large-Relation A R =
  {l1 l2 : Level} (x : A l1) (y : A l2) → is-prop (R x y)

Large-Relation-Prop :
  {α : Level → Level} (β : Level → Level → Level)
  (A : (l : Level) → UU (α l)) →
  UUω
Large-Relation-Prop β A = {l1 l2 : Level} → A l1 → A l2 → Prop (β l1 l2)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop β A)
  where

  large-relation-Large-Relation-Prop : Large-Relation β A
  large-relation-Large-Relation-Prop x y = type-Prop (R x y)

  is-prop-large-relation-Large-Relation-Prop :
    is-prop-Large-Relation A large-relation-Large-Relation-Prop
  is-prop-large-relation-Large-Relation-Prop x y = is-prop-type-Prop (R x y)

  total-space-Large-Relation-Prop : UUω
  total-space-Large-Relation-Prop =
    (l1 l2 : Level) →
    Σ (A l1 × A l2) (λ (a , a') → large-relation-Large-Relation-Prop a a')
```

## Small relations from large relations

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  where

  relation-Large-Relation :
    (R : Large-Relation β A) (l : Level) → Relation (β l l) (A l)
  relation-Large-Relation R l x y = R x y

  relation-prop-Large-Relation-Prop :
    (R : Large-Relation-Prop β A) (l : Level) → Relation-Prop (β l l) (A l)
  relation-prop-Large-Relation-Prop R l x y = R x y

  relation-Large-Relation-Prop :
    (R : Large-Relation-Prop β A) (l : Level) → Relation (β l l) (A l)
  relation-Large-Relation-Prop R =
    relation-Large-Relation (large-relation-Large-Relation-Prop A R)
```

## Specifications of properties of binary relations

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation β A)
  where

  is-reflexive-Large-Relation : UUω
  is-reflexive-Large-Relation = {l : Level} (x : A l) → R x x

  is-symmetric-Large-Relation : UUω
  is-symmetric-Large-Relation =
    {l1 l2 : Level} (x : A l1) (y : A l2) → R x y → R y x

  is-transitive-Large-Relation : UUω
  is-transitive-Large-Relation =
    {l1 l2 l3 : Level} (x : A l1) (y : A l2) (z : A l3) → R y z → R x y → R x z

  is-antisymmetric-Large-Relation : UUω
  is-antisymmetric-Large-Relation =
    {l : Level} → is-antisymmetric (relation-Large-Relation A R l)

  is-antireflexive-Large-Relation : UUω
  is-antireflexive-Large-Relation =
    {l : Level} → (a : A l) → ¬ (R a a)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop β A)
  where

  is-reflexive-Large-Relation-Prop : UUω
  is-reflexive-Large-Relation-Prop =
    is-reflexive-Large-Relation A (large-relation-Large-Relation-Prop A R)

  is-symmetric-Large-Relation-Prop : UUω
  is-symmetric-Large-Relation-Prop =
    is-symmetric-Large-Relation A (large-relation-Large-Relation-Prop A R)

  is-transitive-Large-Relation-Prop : UUω
  is-transitive-Large-Relation-Prop =
    is-transitive-Large-Relation A (large-relation-Large-Relation-Prop A R)

  is-antisymmetric-Large-Relation-Prop : UUω
  is-antisymmetric-Large-Relation-Prop =
    is-antisymmetric-Large-Relation A (large-relation-Large-Relation-Prop A R)

  is-antireflexive-Large-Relation-Prop : UUω
  is-antireflexive-Large-Relation-Prop =
    is-antireflexive-Large-Relation A (large-relation-Large-Relation-Prop A R)

  is-cotransitive-Large-Relation-Prop : UUω
  is-cotransitive-Large-Relation-Prop =
    {l1 l2 l3 : Level} →
    (a : A l1) (b : A l2) (c : A l3) →
    type-Prop (R a b) →
    type-Prop ((R a c) ∨ (R c b))
```

## See also

- [(Small) binary relations](foundation.binary-relations.md)
- [Large preorders](order-theory.large-preorders.md)
- [Large posets](order-theory.large-posets.md)
