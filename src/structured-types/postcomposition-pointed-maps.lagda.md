# Postcomposition of pointed maps

```agda
open import foundation.function-extensionality-axiom

module
  structured-types.postcomposition-pointed-maps
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.pointed-maps funext
open import structured-types.pointed-types
```

</details>

## Idea

The
{{#concept "postcomposition operation" Disambiguation="pointed maps" Agda=postcomp-pointed-map}}
on [pointed maps](structured-types.pointed-maps.md) by a pointed map
`f : A →∗ B` is a family of operations

```text
  f ∘∗ - : (X →∗ A) → (X →∗ B)
```

indexed by a [pointed type](structured-types.pointed-types.md) `X`.

## Definitions

### Postcomposition by pointed maps

```agda
postcomp-pointed-map :
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  (X : Pointed-Type l3) → (X →∗ A) → (X →∗ B)
postcomp-pointed-map f X g = comp-pointed-map f g
```
