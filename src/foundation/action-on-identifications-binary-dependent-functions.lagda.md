# The action on identifications of binary dependent functions

```agda
module foundation.action-on-identifications-binary-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.identity-types
```

</details>

## Idea

Consider a binary dependent function

```text
  f : (x : A) (y : B x) → C x y.
```

The {{#concept "action on identifications" Disambiguation="binary dependent functions" Agda=action-on-identifications-binary-dependent-function}} of `f` on an [identification](foundation-core.identity-types.md) `p : x ＝ x'` in `A` and a [dependent identification](foundation-core.dependent-identifications.md) `q : dependent-identification B p y y'` in `B`, is a _double dependent identification_

```text
  double-dependent-identification C p q (f x y) (f x' y').
```

This double dependent identification is defined by identification elimination on `p`. In the case `p ≐ refl`, the action on identifications of `f` is defined to be `apd (f x) q`.

## Definitions

### The action of binary dependent functions on identifications

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  (f : (x : A) (y : B x) → C x y)
  where

  action-identifications-binary-dependent-function :
    {x x' : A} (p : x ＝ x') {y : B x} {y' : B x'}
    (q : dependent-identification B p y y') →
    double-dependent-identification p q (f x y) (f x' y')
  action-identifications-binary-dependent-function refl q = apd (f _) q
```
