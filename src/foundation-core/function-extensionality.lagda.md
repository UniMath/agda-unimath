# Function extensionality

```agda
module foundation-core.function-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

The function extensionality axiom asserts that identifications of (dependent)
functions are equivalently described as pointwise equalities between them. In
other words, a function is completely determined by its values.

In this file, we define the statement of the axiom. The axiom itself is
postulated in
[`foundation.function-extensionality`](foundation.function-extensionality.md) as
`funext`.

## Statement

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  htpy-eq : {f g : (x : A) → B x} → (f ＝ g) → (f ~ g)
  htpy-eq refl = refl-htpy

  function-extensionality : (f : (x : A) → B x) → UU (l1 ⊔ l2)
  function-extensionality f = (g : (x : A) → B x) → is-equiv (htpy-eq {f} {g})
```

## Properties

### Naturality of `htpy-eq`

```agda
square-htpy-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B) →
  ( g h : B → C) →
  ( (λ (p : (y : B) → g y ＝ h y) (x : A) → p (f x)) ∘ htpy-eq) ~
  ( htpy-eq ∘ (ap (precomp f C)))
square-htpy-eq f g .g refl = refl
```

### The action on paths of an evaluation map

```agda
ap-ev :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (a : A) → {f g : A → B} →
  (p : f ＝ g) → (ap (λ h → h a) p) ＝ htpy-eq p a
ap-ev a refl = refl
```

## See also

- That the univalence axiom implies function extensionality is proven in
  [`foundation.univalence-implies-function-extensionality`](foundation.univalence-implies-function-extensionality.md).
- Weak function extensionality is defined in
  [`foundation.weak-function-extensionality`](foundation.weak-function-extensionality.md).
