# The action on identifications of dependent functions

```agda
module foundation.action-on-identifications-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.identity-types
```

</details>

## Idea

Given a dependent function `f : (x : A) → B x` and an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A`, we
cannot directly compare the values `f x` and `f y`, since `f x` is an element of
type `B x` while `f y` is an element of type `B y`. However, we can
[transport](foundation-core.transport-along-identifications.md) the value `f x`
along `p` to obtain an element of type `B y` that is comparable to the value
`f y`. In other words, we can consider the type of
[dependent identifications](foundation-core.dependent-identifications.md) over
`p` from `f x` to `f y`. The **dependent action on identifications** of `f` on
`p` is a dependent identification

```text
  apd f p : dependent-identification B p (f x) (f y).
```

## Definition

### Functorial action of dependent functions on identity types

```agda
apd :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) {x y : A}
  (p : x ＝ y) → dependent-identification B p (f x) (f y)
apd f refl = refl

apd' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) {x y : A}
  (p : x ＝ y) → dependent-identification' B p (f x) (f y)
apd' f refl = refl
```

## See also

- [Action of functions on identifications](foundation.action-on-identifications-functions.md)
- [Action of functions on higher identifications](foundation.action-on-higher-identifications-functions.md).
- [Action of binary functions on identifications](foundation.action-on-identifications-binary-functions.md).
