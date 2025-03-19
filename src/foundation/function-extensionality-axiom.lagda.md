# The function extensionality axiom

```agda
module foundation.function-extensionality-axiom where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.evaluation-functions
open import foundation.implicit-function-types
open import foundation.universe-levels

open import foundation-core.coherently-invertible-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

The
{{#concept "function extensionality axiom" Agda=function-extensionality Agda=funext}}
asserts that [identifications](foundation-core.identity-types.md) of (dependent)
functions are [equivalently](foundation-core.equivalences.md) described as
[homotopies](foundation-core.homotopies.md) between them. In other words, a
function is completely determined by its values.

Function extensionality is postulated by stating that the canonical map

```text
  htpy-eq : f ＝ g → f ~ g
```

from identifications between two functions to homotopies between them is an
equivalence. The map `htpy-eq` is the unique map that fits in a
[commuting triangle](foundation-core.commuting-triangles-of-maps.md)

```text
              htpy-eq
    (f ＝ g) ----------> (f ~ g)
           \            /
  ap (ev x) \          / ev x
             ∨        ∨
            (f x ＝ g x)
```

In other words, we define

```text
  htpy-eq p x := ap (ev x) p.
```

It follows from this definition that `htpy-eq refl ≐ refl-htpy`, as expected.

## Definitions

### Equalities induce homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  htpy-eq : {f g : (x : A) → B x} → f ＝ g → f ~ g
  htpy-eq p a = ap (ev a) p

  compute-htpy-eq-refl : {f : (x : A) → B x} → htpy-eq refl ＝ refl-htpy' f
  compute-htpy-eq-refl = refl
```

### An instance of function extensionality

This property asserts that, _given_ two functions `f` and `g`, the map

```text
  htpy-eq : f ＝ g → f ~ g
```

is an equivalence.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  instance-function-extensionality : (f g : (x : A) → B x) → UU (l1 ⊔ l2)
  instance-function-extensionality f g = is-equiv (htpy-eq {f = f} {g})
```

### Based function extensionality

This property asserts that, _given_ a function `f`, the map

```text
  htpy-eq : f ＝ g → f ~ g
```

is an equivalence for any function `g` of the same type.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  based-function-extensionality : (f : (x : A) → B x) → UU (l1 ⊔ l2)
  based-function-extensionality f =
    (g : (x : A) → B x) → instance-function-extensionality f g
```

### The function extensionality principle with respect to a universe level

```agda
function-extensionality-Level : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
function-extensionality-Level l1 l2 =
  {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → based-function-extensionality f
```

### The function extensionality axiom

```agda
function-extensionality : UUω
function-extensionality = {l1 l2 : Level} → function-extensionality-Level l1 l2
```

## Properties

### `htpy-eq` preserves inverses

For any two functions `f g : (x : A) → B x` we have a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                  inv
       (f = g) ---------> (g = f)
          |                  |
  htpy-eq |                  | htpy-eq
          ∨                  ∨
       (f ~ g) ---------> (g ~ f).
                inv-htpy
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  compute-htpy-eq-inv : inv-htpy {f = f} {g} ∘ htpy-eq ~ htpy-eq ∘ inv
  compute-htpy-eq-inv refl = refl

  compute-inv-htpy-htpy-eq : htpy-eq ∘ inv ~ inv-htpy {f = f} {g} ∘ htpy-eq
  compute-inv-htpy-htpy-eq = inv-htpy compute-htpy-eq-inv
```

## See also

- The fact that the univalence axiom implies function extensionality is proven
  in
  [`foundation.univalence-implies-function-extensionality`](foundation.univalence-implies-function-extensionality.md).
- Weak function extensionality is defined in
  [`foundation.weak-function-extensionality`](foundation.weak-function-extensionality.md).
- Transporting along homotopies is defined in
  [`foundation.transport-along-homotopies`](foundation.transport-along-homotopies.md).
