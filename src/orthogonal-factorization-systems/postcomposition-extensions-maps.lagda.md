# Postcomposition of extensions of maps

```agda
module orthogonal-factorization-systems.postcomposition-extensions-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.monomorphisms
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.torsorial-type-families

open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

Given a map `i : A → B` and a map `f : A → X`, then we may
{{#concept "postcompose" Disambiguation="extension of map by map" Agda=postcomp-extension}}
any [extension](orthogonal-factorization-systems.extensions-maps.md)
`α : extension i f` by `g` to obtain an extension `g ∘ α : extension i (g ∘ f)`.

## Definition

### Postcomposition of extensions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  postcomp-extension :
    (i : A → B) (f : A → X) (g : X → Y) →
    extension i f → extension i (g ∘ f)
  postcomp-extension i f g =
    map-Σ (is-extension i (g ∘ f)) (postcomp B g) (λ j H → g ·l H)
```

## Properties

### Postcomposition of extensions by an equivalence is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-equiv-postcomp-extension :
    (f : A → B) (i : A → X) (g : X → Y) → is-equiv g →
    is-equiv (postcomp-extension f i g)
  is-equiv-postcomp-extension f i g G =
    is-equiv-map-Σ
      ( is-extension f (g ∘ i))
      ( is-equiv-postcomp-is-equiv g G B)
      ( λ j →
        is-equiv-map-Π-is-fiberwise-equiv
          ( λ x → is-emb-is-equiv G (i x) (j (f x))))

  equiv-postcomp-extension :
    (f : A → B) (i : A → X) (g : X ≃ Y) →
    extension f i ≃ extension f (map-equiv g ∘ i)
  equiv-postcomp-extension f i (g , G) =
    ( postcomp-extension f i g , is-equiv-postcomp-extension f i g G)
```

### Postcomposition of extensions by an embedding is an embedding

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-emb-postcomp-extension :
    (f : A → B) (i : A → X) (g : X → Y) → is-emb g →
    is-emb (postcomp-extension f i g)
  is-emb-postcomp-extension f i g H =
    is-emb-map-Σ
      ( is-extension f (g ∘ i))
      ( is-mono-is-emb g H B)
      ( λ j →
        is-emb-is-equiv
          ( is-equiv-map-Π-is-fiberwise-equiv
            ( λ x → H (i x) (j (f x)))))

  emb-postcomp-extension :
    (f : A → B) (i : A → X) (g : X ↪ Y) →
    extension f i ↪ extension f (map-emb g ∘ i)
  emb-postcomp-extension f i (g , G) =
    postcomp-extension f i g , is-emb-postcomp-extension f i g G
```

### Postcomposition of extensions by a `k`-truncated map is `k`-truncated

```agda
module _
  {l1 l2 l3 l4 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-trunc-map-postcomp-extension :
    (f : A → B) (i : A → X) (g : X → Y) → is-trunc-map k g →
    is-trunc-map k (postcomp-extension f i g)
  is-trunc-map-postcomp-extension f i g G =
    is-trunc-map-Σ k
      ( is-extension f (g ∘ i))
      ( is-trunc-map-postcomp-is-trunc-map k g G B)
      ( λ j →
        is-trunc-map-Π k
          ( λ a → ap g)
          ( λ a → is-trunc-map-ap-is-trunc-map k g G (i a) (j (f a))))

  trunc-map-postcomp-extension :
    (f : A → B) (i : A → X) (g : trunc-map k X Y) →
    trunc-map k (extension f i) (extension f (map-trunc-map g ∘ i))
  trunc-map-postcomp-extension f i (g , G) =
    ( postcomp-extension f i g , is-trunc-map-postcomp-extension f i g G)
```
