# Function extensionality

```agda
module foundation.function-extensionality where

open import foundation-core.function-extensionality public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.implicit-function-types
open import foundation.injective-maps
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.precomposition-functions
```

</details>

## Idea

The {{#concept "function extensionality axiom"}} asserts that
[identifications](foundation-core.identity-types.md) of (dependent) functions
are [equivalently](foundation-core.equivalences.md) described as
[homotopies](foundation-core.homotopies.md) between them. In other words, a
function is completely determined by its values.

## Properties

### Naturality of `eq-htpy` for dependent functions

Consider a map `f : A → B` and two dependent functions `g h : (b : B) → C b`.
Then the square

```text
                     ap (precomp-Π f C)
       (g ＝ h) ---------------------------> (g ∘ f ＝ h ∘ f)
          ^                                         ^
  eq-htpy |                                         | eq-htpy
          |                                         |
       (g ~ h) ----------------------------> (g ∘ f ~ h ∘ f)
                precomp-Π f (eq-value g h)
```

[commutes](foundation-core.commuting-squares-of-maps.md).

```agda
coherence-square-eq-htpy-ap-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) {C : B → UU l3}
  (g h : (b : B) → C b) →
  coherence-square-maps
    ( precomp-Π f (eq-value g h))
    ( eq-htpy)
    ( eq-htpy)
    ( ap (precomp-Π f C) {g} {h})
coherence-square-eq-htpy-ap-precomp-Π f {C = C} g h =
  coherence-square-inv-vertical
    ( ap (precomp-Π f C))
    ( equiv-funext)
    ( equiv-funext)
    ( precomp-Π f (eq-value g h))
    ( coherence-square-htpy-eq-ap-precomp-Π f g h)
```

### Naturality of `eq-htpy` for ordinary functions

Consider a map `f : A → B` and two functions `g h : B → C`. Then the square

```text
                     ap (precomp f C)
       (g ＝ h) -------------------------> (g ∘ f ＝ h ∘ f)
          ^                                       ^
  eq-htpy |                                       | eq-htpy
          |                                       |
       (g ~ h) --------------------------> (g ∘ f ~ h ∘ f)
                precomp f (eq-value g h)
```

commutes.

```agda
coherence-square-eq-htpy-ap-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : A → B) (g h : B → C) →
  coherence-square-maps
    ( precomp-Π f (eq-value g h))
    ( eq-htpy)
    ( eq-htpy)
    ( ap (precomp f C))
coherence-square-eq-htpy-ap-precomp {C = C} f g h =
  coherence-square-inv-vertical
    ( ap (precomp f C))
    ( equiv-funext)
    ( equiv-funext)
    ( precomp-Π f (eq-value g h))
    ( coherence-square-htpy-eq-ap-precomp f g h)
```

### `eq-htpy` preserves inverses

In other words, we have a commutative diagram

```text
                  inv
       (f ＝ g) --------> (g ＝ f)
          ^                  ^
  eq-htpy |                  | eq-htpy
          |                  |
       (f ~ g) ---------> (g ~ f).
                inv-htpy
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  compute-eq-htpy-inv-htpy :
    inv ∘ eq-htpy ~ eq-htpy ∘ inv-htpy {f = f} {g}
  compute-eq-htpy-inv-htpy =
    coherence-square-inv-vertical
      ( inv)
      ( equiv-funext)
      ( equiv-funext)
      ( inv-htpy)
      ( compute-htpy-eq-inv)

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
