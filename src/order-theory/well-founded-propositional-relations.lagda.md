# Well-founded propositional relations

```agda
module order-theory.well-founded-propositional-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universal-quantification
open import foundation.universe-levels

open import order-theory.accessible-elements-relations
open import order-theory.preorders
open import order-theory.well-founded-relations
```

</details>

## Idea

Given a type `X` equipped with a
[binary propositional relation](foundation.binary-relations.md)
`_<_ : X → X → Prop` we say that the relation `_<_` is
{{#concept "well-founded" Disambiguation="binary propositional relation" WDID=Q338021 WD="well-founded relation" Agda=is-well-founded-Relation-Prop Agda=Well-Founded-Relation-Prop}}
if all elements of `X` are
[accessible](order-theory.accessible-elements-relations.md) with respect to
`_<_`.

Well-founded propositional relations satisfy an induction principle: In order to
construct an element of `P x` for all `x : X` it suffices to construct an
element of `P y` for all elements `y < x`. More precisely, the
{{#concept "well-founded induction principle" WDID=Q14402036 WD="well-founded induction" Agda=ind-Well-Founded-Relation-Prop}}
is a function

```text
  (x : X) → ((u : X) → (u < x) → P u) → P x.
```

## Definitions

### The predicate of being a well-founded propositional relation

```agda
module _
  {l1 l2 : Level} {X : UU l1} (_<_ : Relation-Prop l2 X)
  where

  is-well-founded-prop-Relation-Prop : Prop (l1 ⊔ l2)
  is-well-founded-prop-Relation-Prop =
    is-well-founded-prop-Relation (rel-Relation-Prop _<_)

  is-well-founded-Relation-Prop : UU (l1 ⊔ l2)
  is-well-founded-Relation-Prop = type-Prop is-well-founded-prop-Relation-Prop

  is-prop-is-well-founded-Relation-Prop : is-prop is-well-founded-Relation-Prop
  is-prop-is-well-founded-Relation-Prop =
    is-prop-type-Prop is-well-founded-prop-Relation-Prop
```

### Well-founded propositional relations

```agda
Well-Founded-Relation-Prop :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Well-Founded-Relation-Prop l X =
  Σ (Relation-Prop l X) is-well-founded-Relation-Prop

module _
  {l1 l2 : Level} {X : UU l1} (R : Well-Founded-Relation-Prop l2 X)
  where

  rel-prop-Well-Founded-Relation-Prop : Relation-Prop l2 X
  rel-prop-Well-Founded-Relation-Prop = pr1 R

  rel-Well-Founded-Relation-Prop : Relation l2 X
  rel-Well-Founded-Relation-Prop =
    rel-Relation-Prop rel-prop-Well-Founded-Relation-Prop

  is-well-founded-Well-Founded-Relation-Prop :
    is-well-founded-Relation-Prop rel-prop-Well-Founded-Relation-Prop
  is-well-founded-Well-Founded-Relation-Prop = pr2 R
```

### Well-founded induction

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  ((R , w) : Well-Founded-Relation-Prop l2 X)
  (let _<_ = rel-Relation-Prop R)
  (P : X → UU l3)
  where

  ind-Well-Founded-Relation-Prop :
    ({x : X} → ({y : X} → y < x → P y) → P x) → (x : X) → P x
  ind-Well-Founded-Relation-Prop IH x =
    ind-accessible-element-Relation _<_ P (λ _ → IH) (w x)
```

## Properties

### A well-founded propositional relation is asymmetric, and thus irreflexive

```agda
module _
  {l1 l2 : Level} {X : UU l1} ((R , w) : Well-Founded-Relation-Prop l2 X)
  (let _<_ = rel-Relation-Prop R)
  where

  is-asymmetric-le-Well-Founded-Relation-Prop : is-asymmetric _<_
  is-asymmetric-le-Well-Founded-Relation-Prop x y =
    is-asymmetric-is-accessible-element-Relation _<_ (w x)

  is-irreflexive-le-Well-Founded-Relation-Prop : is-irreflexive _<_
  is-irreflexive-le-Well-Founded-Relation-Prop =
    is-irreflexive-is-asymmetric _<_ is-asymmetric-le-Well-Founded-Relation-Prop
```

### The associated reflexive propositional relation of a well-founded propositional relation

Given a well-founded relation $<$ on $X$ there is an associated reflexive
relation given by

$$
  (x ≤ y) := ∀ (u : X), (u < x) ⇒ (u < y).
$$

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  ((_<_ , w) : Well-Founded-Relation-Prop l2 X)
  where

  leq-prop-Well-Founded-Relation-Prop : Relation-Prop (l1 ⊔ l2) X
  leq-prop-Well-Founded-Relation-Prop x y = ∀' X (λ u → u < x ⇒ u < y)

  leq-Well-Founded-Relation-Prop : Relation (l1 ⊔ l2) X
  leq-Well-Founded-Relation-Prop =
    rel-Relation-Prop leq-prop-Well-Founded-Relation-Prop

  refl-leq-Well-Founded-Relation-Prop :
    is-reflexive leq-Well-Founded-Relation-Prop
  refl-leq-Well-Founded-Relation-Prop x u = id

  leq-eq-Well-Founded-Relation-Prop :
    {x y : X} → x ＝ y → leq-Well-Founded-Relation-Prop x y
  leq-eq-Well-Founded-Relation-Prop {x} refl =
    refl-leq-Well-Founded-Relation-Prop x

  transitive-leq-Well-Founded-Relation-Prop :
    is-transitive leq-Well-Founded-Relation-Prop
  transitive-leq-Well-Founded-Relation-Prop x y z f g t H = f t (g t H)
```

## See also

- [Well-founded relations](order-theory.well-founded-relations.md).
