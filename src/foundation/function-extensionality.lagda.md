# Function extensionality

```agda
module foundation.function-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.evaluation-functions
open import foundation.implicit-function-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
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

postulate
  funext : function-extensionality

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-funext : {f g : (x : A) → B x} → (f ＝ g) ≃ (f ~ g)
  pr1 (equiv-funext) = htpy-eq
  pr2 (equiv-funext {f} {g}) = funext f g

  eq-htpy : {f g : (x : A) → B x} → f ~ g → f ＝ g
  eq-htpy {f} {g} = map-inv-is-equiv (funext f g)

  abstract
    is-section-eq-htpy :
      {f g : (x : A) → B x} → (htpy-eq ∘ eq-htpy {f} {g}) ~ id
    is-section-eq-htpy {f} {g} = is-section-map-inv-is-equiv (funext f g)

    is-retraction-eq-htpy :
      {f g : (x : A) → B x} → (eq-htpy ∘ htpy-eq {f = f} {g = g}) ~ id
    is-retraction-eq-htpy {f} {g} = is-retraction-map-inv-is-equiv (funext f g)

    is-equiv-eq-htpy :
      (f g : (x : A) → B x) → is-equiv (eq-htpy {f} {g})
    is-equiv-eq-htpy f g = is-equiv-map-inv-is-equiv (funext f g)

    eq-htpy-refl-htpy :
      (f : (x : A) → B x) → eq-htpy (refl-htpy {f = f}) ＝ refl
    eq-htpy-refl-htpy f = is-retraction-eq-htpy refl

  equiv-eq-htpy : {f g : (x : A) → B x} → (f ~ g) ≃ (f ＝ g)
  pr1 (equiv-eq-htpy {f} {g}) = eq-htpy
  pr2 (equiv-eq-htpy {f} {g}) = is-equiv-eq-htpy f g
```

### Function extensionality for implicit functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : {x : A} → B x}
  where

  equiv-funext-implicit :
    (Id {A = {x : A} → B x} f g) ≃ ((x : A) → f {x} ＝ g {x})
  equiv-funext-implicit =
    equiv-funext ∘e equiv-ap equiv-explicit-implicit-Π f g

  htpy-eq-implicit :
    Id {A = {x : A} → B x} f g → (x : A) → f {x} ＝ g {x}
  htpy-eq-implicit = map-equiv equiv-funext-implicit

  funext-implicit : is-equiv htpy-eq-implicit
  funext-implicit = is-equiv-map-equiv equiv-funext-implicit

  eq-htpy-implicit :
    ((x : A) → f {x} ＝ g {x}) → Id {A = {x : A} → B x} f g
  eq-htpy-implicit = map-inv-equiv equiv-funext-implicit
```

## Properties

### `htpy-eq` preserves concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  htpy-eq-concat :
    (p : f ＝ g) (q : g ＝ h) → htpy-eq (p ∙ q) ＝ htpy-eq p ∙h htpy-eq q
  htpy-eq-concat refl refl = refl
```

### `eq-htpy` preserves concatenation of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  eq-htpy-concat-htpy :
    (H : f ~ g) (K : g ~ h) → eq-htpy (H ∙h K) ＝ (eq-htpy H ∙ eq-htpy K)
  eq-htpy-concat-htpy H K =
      ( ap
        ( eq-htpy)
        ( inv (ap-binary _∙h_ (is-section-eq-htpy H) (is-section-eq-htpy K)) ∙
          inv (htpy-eq-concat (eq-htpy H) (eq-htpy K)))) ∙
      ( is-retraction-eq-htpy (eq-htpy H ∙ eq-htpy K))
```

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

### `eq-htpy` preserves inverses

For any two functions `f g : (x : A) → B x` we have a commuting square

```text
                inv-htpy
       (f ~ g) ---------> (g ~ f)
          |                  |
  eq-htpy |                  | eq-htpy
          ∨                  ∨
       (f = g) ---------> (g = f).
                  inv
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  compute-eq-htpy-inv-htpy :
    inv ∘ eq-htpy ~ eq-htpy ∘ inv-htpy {f = f} {g}
  compute-eq-htpy-inv-htpy H =
    ( inv (is-retraction-eq-htpy _)) ∙
    ( inv (ap eq-htpy (compute-htpy-eq-inv (eq-htpy H))) ∙
      ap (eq-htpy ∘ inv-htpy) (is-section-eq-htpy _))

  compute-inv-eq-htpy :
    eq-htpy ∘ inv-htpy {f = f} {g} ~ inv ∘ eq-htpy
  compute-inv-eq-htpy = inv-htpy compute-eq-htpy-inv-htpy
```

## See also

- The fact that the univalence axiom implies function extensionality is proven
  in
  [`foundation.univalence-implies-function-extensionality`](foundation.univalence-implies-function-extensionality.md).
- Weak function extensionality is defined in
  [`foundation.weak-function-extensionality`](foundation.weak-function-extensionality.md).
- Transporting along homotopies is defined in
  [`foundation.transport-along-homotopies`](foundation.transport-along-homotopies.md).
