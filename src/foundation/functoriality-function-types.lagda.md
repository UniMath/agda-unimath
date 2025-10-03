# Functoriality of function types

```agda
module foundation.functoriality-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-function-types
open import foundation.postcomposition-functions
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.propositional-maps
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels
```

</details>

## Properties

### Equivalent types have equivalent function types

```agda
module _
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : UU l2} {A : UU l3} (B : UU l4)
  ( e : A' ≃ A) (f : B' ≃ B)
  where

  map-equiv-function-type : (A' → B') → (A → B)
  map-equiv-function-type h = map-equiv f ∘ (h ∘ map-inv-equiv e)

  compute-map-equiv-function-type :
    (h : A' → B') (x : A') →
    map-equiv-function-type h (map-equiv e x) ＝ map-equiv f (h x)
  compute-map-equiv-function-type h x =
    ap (map-equiv f ∘ h) (is-retraction-map-inv-equiv e x)

  is-equiv-map-equiv-function-type : is-equiv map-equiv-function-type
  is-equiv-map-equiv-function-type =
    is-equiv-comp
      ( precomp (map-equiv (inv-equiv e)) B)
      ( postcomp A' (map-equiv f))
      ( is-equiv-postcomp-equiv f A')
      ( is-equiv-precomp-equiv (inv-equiv e) B)

  equiv-function-type : (A' → B') ≃ (A → B)
  pr1 equiv-function-type = map-equiv-function-type
  pr2 equiv-function-type = is-equiv-map-equiv-function-type
```

### A map is truncated iff postcomposition by it is truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-trunc-map-postcomp-is-trunc-map :
    is-trunc-map k f →
    {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)
  is-trunc-map-postcomp-is-trunc-map is-trunc-f A =
    is-trunc-map-Π' k (terminal-map A) (point f) (point is-trunc-f)

  is-trunc-map-is-trunc-map-postcomp :
    ({l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
    is-trunc-map k f
  is-trunc-map-is-trunc-map-postcomp is-trunc-postcomp-f =
    is-trunc-map-is-trunc-map-Π' k
      ( point f)
      ( λ {l} {J} α → is-trunc-postcomp-f {l} J)
      ( star)

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-emb-postcomp-is-emb :
    is-emb f →
    {l3 : Level} (A : UU l3) → is-emb (postcomp A f)
  is-emb-postcomp-is-emb is-emb-f A =
    is-emb-is-prop-map
      ( is-trunc-map-postcomp-is-trunc-map neg-one-𝕋 f
        ( is-prop-map-is-emb is-emb-f)
        ( A))

  is-emb-is-emb-postcomp :
    ({l3 : Level} (A : UU l3) → is-emb (postcomp A f)) →
    is-emb f
  is-emb-is-emb-postcomp is-emb-postcomp-f =
    is-emb-is-prop-map
      ( is-trunc-map-is-trunc-map-postcomp neg-one-𝕋 f
        ( is-prop-map-is-emb ∘ is-emb-postcomp-f))

emb-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ Y) (A : UU l3) →
  (A → X) ↪ (A → Y)
pr1 (emb-postcomp f A) = postcomp A (map-emb f)
pr2 (emb-postcomp f A) = is-emb-postcomp-is-emb (map-emb f) (is-emb-map-emb f) A
```

## See also

- Functorial properties of dependent function types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
