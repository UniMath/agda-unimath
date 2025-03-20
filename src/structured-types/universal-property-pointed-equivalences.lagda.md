# The universal property of pointed equivalences

```agda
open import foundation.function-extensionality-axiom

module
  structured-types.universal-property-pointed-equivalences
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences funext
open import foundation.universe-levels

open import structured-types.pointed-maps funext
open import structured-types.pointed-types
open import structured-types.precomposition-pointed-maps funext
```

</details>

## Idea

Analogous to the
[universal property of equivalences](foundation.universal-property-equivalences.md),
the
{{#concept "universal property of pointed equivalences" Agda=universal-property-pointed-equiv}}
asserts about a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B`
that the
[precomposition function](structured-types.precomposition-pointed-maps.md)

```text
  - ∘∗ f : (B →∗ C) → (A →∗ C)
```

is an [equivalence](foundation.equivalences.md) for every
[pointed type](structured-types.pointed-types.md) `C`.

## Definitions

### The universal property of pointed equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  universal-property-pointed-equiv : UUω
  universal-property-pointed-equiv =
    {l : Level} (C : Pointed-Type l) → is-equiv (precomp-pointed-map f C)
```
