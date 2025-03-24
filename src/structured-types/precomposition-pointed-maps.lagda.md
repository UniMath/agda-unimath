# Precomposition of pointed maps

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.precomposition-pointed-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.pointed-maps funext univalence truncations
open import structured-types.pointed-types
```

</details>

## Idea

The
{{#concept "precomposition operation" Disambiguation="pointed maps" Agda=precomp-pointed-map}}
on [pointed maps](structured-types.pointed-maps.md) by a pointed map
`f : A →∗ B` is a family of operations

```text
  - ∘∗ f : (B →∗ C) → (A →∗ C)
```

indexed by a [pointed type](structured-types.pointed-types.md) `C`.

## Definitions

### Precomposition by pointed maps

```agda
precomp-pointed-map :
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  (C : Pointed-Type l3) → (B →∗ C) → (A →∗ C)
precomp-pointed-map f C g = comp-pointed-map g f
```
