# Evaluation of functions

```agda
module foundation.evaluation-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Consider a family of types `B` over `A` and let `a : A` be an element. The
{{#concept "evaluation function" Agda=ev}} at `a`

```text
  ev : ((x : A) → B x) → B a
```

is the map given by `f ↦ f a`, evaluating dependent functions at `a`.

## Definitions

### The evaluation function

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A)
  where

  ev : ((x : A) → B x) → B a
  ev f = f a
```

### The evaluation function with an explicit type family

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  ev-dependent-function : ((x : A) → B x) → B a
  ev-dependent-function = ev a
```

### The evaluation function for nondependent functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2) (a : A)
  where

  ev-function : (A → B) → B
  ev-function = ev a
```

### The evaluation function of implicit functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A)
  where

  ev-implicit-function : ({x : A} → B x) → B a
  ev-implicit-function f = f {a}
```

### The evaluation function of implicit function, specified with an explicit type family

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  ev-implicit-function' : ({x : A} → B x) → B a
  ev-implicit-function' = ev-implicit-function a
```

## Properties

### The action on paths of an evaluation map

For any two functions `f g : A → B`, the action on identifications of
`ev-function B a`

```text
  ap (ev-function B a) : (f ＝ g) → (f a ＝ g a)
```

is homotopic to the map `p ↦ htpy-eq p a`, where `htpy-eq` is the operation that
constructs a homotopy from an identification of functions, which we constructed
in [foundation.function-extensionality. In other words, the triangle of maps

```text
                          htpy-eq
               (f ＝ g) ----------> (f ~ g)
                      \            /
  ap (ev-function B a) \          / ev a
                        ∨        ∨
                       (f a ＝ g a)
```

[commutes](foundation-core.commuting-triangles-of-maps.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (a : A)
  where

  ap-ev : {f g : A → B} (p : f ＝ g) → (ap (ev-function B a) p) ＝ htpy-eq p a
  ap-ev refl = refl
```
