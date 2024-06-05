# Path-cosplit maps

```agda
module foundation.path-cosplit-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.iterated-dependent-product-types
open import foundation.logical-equivalences
open import foundation.mere-path-cosplit-maps
open import foundation.propositional-truncations
open import foundation.truncated-maps
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.truncated-types
```

</details>

## Idea

In Homotopy Type Theory, there are multiple nonequivalent ways to state that a
map is "injective" that are more or less informed by the homotopy structures of
its domain and codomain. A
{{#concept "path-cosplit map" Disambiguation="between types" Agda=is-path-cosplit}}
is one such notion, lying somewhere between
[embeddings](foundation-core.embeddings.md) and
[injective maps](foundation-core.injective-maps.md). In fact, given an integer
`k ≥ -2`, if we understand `k`-injective map to mean the `k+2`-dimensional
[action on identifications](foundation.action-on-higher-identifications-functions.md)
has a converse map, then we have proper inclusions

```text
  k-injective maps ⊃ k-path-cosplit maps ⊃ k-truncated maps.
```

While `k`-truncatedness answers the question:

> At which dimension is the action on higher identifications of a function
> always an [equivalence](foundation-core.equivalences.md)?

Being `k`-path-cosplitting instead answers the question:

> At which dimension is the action a
> [retract](foundation-core.retracts-of-types.md)?

Thus a _-2-path-cosplit map_ is a map equipped with a
[retraction](foundation-core.retractions.md). A _`k+1`-path-cosplit map_ is a
map whose
[action on identifications](foundation.action-on-identifications-functions.md)
is `k`-path-cosplit.

We show that `k`-path-cosplittness coincides with `k`-truncatedness when the
codomain is `k`-truncated, but more generally `k`-path-cosplitting may only
induce retracts on higher homotopy groups.

## Definitions

```agda
is-path-cosplit :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-path-cosplit neg-two-𝕋 f = retraction f
is-path-cosplit (succ-𝕋 k) {A} f = (x y : A) → is-path-cosplit k (ap f {x} {y})
```

## Properties

### If a map is `k`-path-cosplit it is merely `k`-path-cosplit

```agda
is-mere-path-cosplit-is-path-cosplit :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-path-cosplit k f → is-mere-path-cosplit k f
is-mere-path-cosplit-is-path-cosplit neg-two-𝕋 is-cosplit-f =
  unit-trunc-Prop is-cosplit-f
is-mere-path-cosplit-is-path-cosplit (succ-𝕋 k) is-cosplit-f x y =
  is-mere-path-cosplit-is-path-cosplit k (is-cosplit-f x y)
```

### If a map is `k`-truncated then it is `k`-path-cosplit

```agda
is-path-cosplit-is-trunc :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-trunc-map k f → is-path-cosplit k f
is-path-cosplit-is-trunc neg-two-𝕋 is-trunc-f =
  retraction-is-contr-map is-trunc-f
is-path-cosplit-is-trunc (succ-𝕋 k) {f = f} is-trunc-f x y =
  is-path-cosplit-is-trunc k (is-trunc-map-ap-is-trunc-map k f is-trunc-f x y)
```

### If a map is `k`-path-cosplit then it is `k+1`-path-cosplit

```agda
is-path-cosplit-succ-is-path-cosplit :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-path-cosplit k f → is-path-cosplit (succ-𝕋 k) f
is-path-cosplit-succ-is-path-cosplit neg-two-𝕋 {f = f} is-cosplit-f x y =
  retraction-ap f is-cosplit-f
is-path-cosplit-succ-is-path-cosplit (succ-𝕋 k) is-cosplit-f x y =
  is-path-cosplit-succ-is-path-cosplit k (is-cosplit-f x y)
```

### If a type maps into a `k`-truncted type via a `k`-path-cosplit map then it is `k`-truncated

```agda
is-trunc-domain-is-path-cosplit-is-trunc-codomain :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-trunc k B → is-path-cosplit k f → is-trunc k A
is-trunc-domain-is-path-cosplit-is-trunc-codomain neg-two-𝕋
  {A} {B} {f} is-trunc-B is-cosplit-f =
  is-trunc-retract-of (f , is-cosplit-f) is-trunc-B
is-trunc-domain-is-path-cosplit-is-trunc-codomain
  (succ-𝕋 k) {A} {B} {f} is-trunc-B is-cosplit-f x y =
  is-trunc-domain-is-path-cosplit-is-trunc-codomain k
    ( is-trunc-B (f x) (f y))
    ( is-cosplit-f x y)
```

This result generalizes the following statements:

- A type that injects into a set is a set.

- A type that embeds into a `k+1`-truncated type is `k+1`-truncated.

- A type that maps into a `k`-truncated type via a `k`-truncated map is
  `k`-truncated.

### If the codomain of a `k`-path-cosplit map is `k`-truncated then the map is `k`-truncated

```agda
is-trunc-map-is-path-cosplit-is-trunc-codomain :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-trunc k B → is-path-cosplit k f → is-trunc-map k f
is-trunc-map-is-path-cosplit-is-trunc-codomain k is-trunc-B is-cosplit-f =
  is-trunc-map-is-trunc-domain-codomain k
    ( is-trunc-domain-is-path-cosplit-is-trunc-codomain k
      ( is-trunc-B)
      ( is-cosplit-f))
    ( is-trunc-B)
```

## See also

- [Mere path-cosplit maps](foundation.mere-path-cosplit-maps.md)
- [Path-split maps](foundation.path-cosplit-maps.md)
- [Injective maps](foundation-core.injective-maps.md)
- [Truncated maps](foundation-core.truncated-maps.md)
- [Embeddings](foundation-core.embeddings.md)
