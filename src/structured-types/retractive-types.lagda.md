# Retractive types

```agda
module structured-types.retractive-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A {{#concept "retractive type" Agda=Retractive-Type}} `A` under `X`, or
**`X`-retractive type** is the data of displaying `X` as a retract of `A`. I.e.,
it is a pair of maps

```text
      a       p
  X ----> A ----> X
```

such that the composite `r ∘ a` is the identity. We refer to `a` as the
_inclusion_, or _section_, of `A` and `p` as the _retraction_, or _projection_.

Retractive types are also known as **ex-spaces**, and form the basic objects in
the study of parametrized homotopy theory {{#cite MS04}}. Observe that under
[type duality](foundation.type-duality.md) retractive types correspond precisely
to families of [pointed types](structured-types.pointed-types.md), hence the
study of retractive types is the study of pointed types parametrized over the
base type `X`.

`X`-Retractive types live naturally in the [coslice](foundation.coslice.md) of
`X`, which is why we use the preposition _under_, rather than _over_.

## Definitions

### The predicate that a type is retractive under `X`

```agda
module _
  {l1 l2 : Level} (X : UU l1) (A : UU l2)
  where

  is-retractive-under : UU (l1 ⊔ l2)
  is-retractive-under = X retract-of A
```

### The universe of retractive types under `X`

```agda
Retractive-Type : {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
Retractive-Type l2 X = Σ (UU l2) (is-retractive-under X)

module _
  {l1 l2 : Level} {X : UU l1} (A : Retractive-Type l2 X)
  where

  type-Retractive-Type : UU l2
  type-Retractive-Type = pr1 A

  retract-Retractive-Type : X retract-of type-Retractive-Type
  retract-Retractive-Type = pr2 A

  inclusion-Retractive-Type : X → type-Retractive-Type
  inclusion-Retractive-Type = inclusion-retract retract-Retractive-Type

  retraction-Retractive-Type : retraction inclusion-Retractive-Type
  retraction-Retractive-Type = retraction-retract retract-Retractive-Type

  map-retraction-Retractive-Type : type-Retractive-Type → X
  map-retraction-Retractive-Type =
    map-retraction-retract retract-Retractive-Type

  is-retract-Retractive-Type :
    is-retraction inclusion-Retractive-Type map-retraction-Retractive-Type
  is-retract-Retractive-Type =
    is-retraction-map-retraction-retract retract-Retractive-Type

  section-Retractive-Type : section map-retraction-Retractive-Type
  section-Retractive-Type =
    (inclusion-Retractive-Type , is-retract-Retractive-Type)
```

### Evaluation at the inclusion/section

```agda
ev-Retractive-Type :
  {l1 l2 l3 : Level} {X : UU l1} (A : Retractive-Type l2 X) {B : X → UU l3} →
  ((a : type-Retractive-Type A) → B (map-retraction-Retractive-Type A a)) →
  (x : X) → B x
ev-Retractive-Type A {B} f x =
  tr B (is-retract-Retractive-Type A x) (f (inclusion-Retractive-Type A x))
```

## See also

- In [pointed type duality](structured-types.pointed-type-duality.md) we show
  that retractive types under `X` are equivalent to families of
  [pointed types](structured-types.pointed-types.md) over `X`.

## References

{{#bibliography}}
