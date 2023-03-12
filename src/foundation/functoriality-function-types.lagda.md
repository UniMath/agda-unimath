# Functoriality of function types

```agda
module foundation.functoriality-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.functoriality-function-types public

open import foundation.constant-maps
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.truncated-maps
open import foundation-core.truncation-levels
```

</details>

## Properties

```agda
is-trunc-map-postcomp-is-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-trunc-map k f → is-trunc-map k (postcomp A f)
is-trunc-map-postcomp-is-trunc-map k A {X} {Y} f is-trunc-f =
  is-trunc-map-map-Π-is-trunc-map' k
    ( const A unit star)
    ( const unit (X → Y) f)
    ( const unit (is-trunc-map k f) is-trunc-f)

is-trunc-map-is-trunc-map-postcomp :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y) →
  ( {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
  is-trunc-map k f
is-trunc-map-is-trunc-map-postcomp k {X} {Y} f is-trunc-post-f =
  is-trunc-map-is-trunc-map-map-Π' k
    ( const unit (X → Y) f)
    ( λ {l} {J} α → is-trunc-post-f {l} J)
    ( star)
```

## See also

- Functorial properties of dependent function types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
