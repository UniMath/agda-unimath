# Monomorphisms

```agda
module foundation.monomorphisms where

open import foundation-core.monomorphisms public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.logical-equivalences
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.raising-universe-levels
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.small-types
```

</details>

## Idea

A function `f : A → B` is a
{{#concept "monomorphism" Disambiguation="of types" Agda=is-mono}} if whenever
we have two functions `g h : X → A` such that `f ∘ g = f ∘ h`, then in fact
`g = h`. The correct way to state this in Homotopy Type Theory is to say that
[postcomposition](foundation-core.postcomposition-functions.md) by `f` is an
[embedding](foundation-core.embeddings.md).

## Properties

### Smallness of the mono predicate

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-mono-is-mono-lub : (l3 l4 : Level) → is-mono (l3 ⊔ l4) f → is-mono l3 f
  is-mono-is-mono-lub l3 l4 H X =
    is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps
      ( postcomp (raise l4 X) f)
      ( precomp map-raise A)
      ( precomp map-raise B)
      ( postcomp X f)
      ( refl-htpy)
      ( is-equiv-precomp-is-equiv map-raise is-equiv-map-raise A)
      ( is-equiv-precomp-is-equiv map-raise is-equiv-map-raise B)
      ( H (raise l4 X))

  is-emb-is-mono-Level : {l3 : Level} → is-mono l3 f → is-emb f
  is-emb-is-mono-Level {l3} H =
    is-emb-is-mono-lzero f (is-mono-is-mono-lub lzero l3 H)

  is-emb-iff-is-mono : {l3 : Level} → is-mono l3 f ↔ is-emb f
  is-emb-iff-is-mono = (is-emb-is-mono-Level , (λ H → is-mono-is-emb f H))

  equiv-is-emb-is-mono : {l3 : Level} → is-mono l3 f ≃ is-emb f
  equiv-is-emb-is-mono {l3} =
    equiv-iff'
      ( is-mono-Prop l3 f)
      ( is-emb-Prop f)
      ( is-emb-iff-is-mono)

  is-small-is-mono : {l3 : Level} → is-small (l1 ⊔ l2) (is-mono l3 f)
  is-small-is-mono = (is-emb f , equiv-is-emb-is-mono)
```
