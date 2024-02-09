# Well-founded relations

```agda
module order-theory.well-founded-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.accessible-elements-relations
```

</details>

## Idea

Given a type `X` equipped with a
[binary relation](foundation.binary-relations.md) `_ϵ_ : X → X → Type` we say
that the relation `_ϵ_` is **well-founded** if all elements of `X` are
[accessible](order-theory.accessible-elements-relations.md) with respect to
`_ϵ_`.

Well-founded relations satisfy an induction principle: In order to construct an
element of `P x` for all `x : X` it suffices to construct an element of `P y`
for all elements `y ϵ x`. More precisely, the **well-founded induction
principle** is a function

```text
  (x : X) → ((y : Y) → y ϵ x → P y) → P x.
```

## Definitions

### The predicate of being a well-founded relation

```agda
module _
  {l1 l2 : Level} {X : UU l1} (_ϵ_ : Relation l2 X)
  where

  is-well-founded-prop-Relation : Prop (l1 ⊔ l2)
  is-well-founded-prop-Relation =
    Π-Prop X (is-accessible-element-prop-Relation _ϵ_)

  is-well-founded-Relation : UU (l1 ⊔ l2)
  is-well-founded-Relation = (x : X) → is-accessible-element-Relation _ϵ_ x
```

### Well-founded relations

```agda
Well-Founded-Relation : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Well-Founded-Relation l X = Σ (Relation l X) is-well-founded-Relation

module _
  {l1 l2 : Level} {X : UU l1} (R : Well-Founded-Relation l2 X)
  where

  rel-Well-Founded-Relation : Relation l2 X
  rel-Well-Founded-Relation = pr1 R

  is-well-founded-Well-Founded-Relation :
    is-well-founded-Relation rel-Well-Founded-Relation
  is-well-founded-Well-Founded-Relation = pr2 R
```

## Properties

### Well-founded induction

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} ((_ϵ_ , w) : Well-Founded-Relation l2 X)
  (P : X → UU l3)
  where

  ind-Well-Founded-Relation :
    ({x : X} → ({y : X} → y ϵ x → P y) → P x) → (x : X) → P x
  ind-Well-Founded-Relation IH x =
    ind-accessible-element-Relation _ϵ_ P (λ _ → IH) (w x)
```

### A well-founded relation is asymmetric (and thus irreflexive)

```agda
module _
  {l1 l2 : Level} {X : UU l1} ((_ϵ_ , w) : Well-Founded-Relation l2 X)
  where

  is-asymmetric-Well-Founded-Relation :
    is-asymmetric _ϵ_
  is-asymmetric-Well-Founded-Relation x y =
    is-asymmetric-is-accessible-element-Relation _ϵ_ (w x)

module _
  {l1 l2 : Level} {X : UU l1} (ϵ : Well-Founded-Relation l2 X)
  where

  is-irreflexive-Well-Founded-Relation :
    is-irreflexive (rel-Well-Founded-Relation ϵ)
  is-irreflexive-Well-Founded-Relation =
    is-irreflexive-is-asymmetric
      ( rel-Well-Founded-Relation ϵ)
      ( is-asymmetric-Well-Founded-Relation ϵ)
```
