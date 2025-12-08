# Monomorphisms

```agda
module foundation.monomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-extensionality
open import foundation.functoriality-function-types
open import foundation.logical-equivalences
open import foundation.postcomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.equivalences-arrows
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.truncation-levels
```

</details>

## Idea

A function `f : A → B` is a
{{#concept "monomorphism" Disambiguation="of types" Agda=is-mono}} if whenever
we have two functions `g h : X → A` such that `f ∘ g = f ∘ h`, then in fact
`g = h`. The correct way to state this in Homotopy Type Theory is to say that
[postcomposition](foundation-core.postcomposition-functions.md) by `f` is an
[embedding](foundation-core.embeddings.md).

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-mono-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-Prop = Π-Prop (UU l3) (λ X → is-emb-Prop (postcomp X f))

  is-mono : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono = type-Prop is-mono-Prop

  is-prop-is-mono : is-prop is-mono
  is-prop-is-mono = is-prop-type-Prop is-mono-Prop
```

## Properties

If `f : A → B` is a monomorphism then for any `g h : X → A` we have an
equivalence `(f ∘ g = f ∘ h) ≃ (g = h)`. In particular, if `f ∘ g = f ∘ h` then
`g = h`.

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  (p : is-mono l3 f) {X : UU l3} (g h : X → A)
  where

  equiv-postcomp-is-mono : (g ＝ h) ≃ (f ∘ g ＝ f ∘ h)
  pr1 equiv-postcomp-is-mono = ap (f ∘_)
  pr2 equiv-postcomp-is-mono = p X g h

  is-injective-postcomp-is-mono : f ∘ g ＝ f ∘ h → g ＝ h
  is-injective-postcomp-is-mono = map-inv-equiv equiv-postcomp-is-mono
```

A function is a monomorphism if and only if it is an embedding.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-mono-is-emb : is-emb f → {l3 : Level} → is-mono l3 f
  is-mono-is-emb is-emb-f X =
    is-emb-is-prop-map
      ( is-trunc-map-postcomp-is-trunc-map neg-one-𝕋 f
        ( is-prop-map-is-emb is-emb-f)
        ( X))

  is-emb-is-mono-lzero : is-mono lzero f → is-emb f
  is-emb-is-mono-lzero is-mono-f =
    is-emb-is-prop-map
      ( is-trunc-map-is-trunc-map-postcomp-lzero neg-one-𝕋 f
        ( λ X → is-prop-map-is-emb (is-mono-f X)))

  is-emb-is-mono : ({l3 : Level} → is-mono l3 f) → is-emb f
  is-emb-is-mono is-mono-f =
    is-emb-is-mono-lzero is-mono-f

  equiv-postcomp-is-emb :
    is-emb f →
    {l3 : Level} {X : UU l3} (g h : X → A) → (g ＝ h) ≃ (f ∘ g ＝ f ∘ h)
  equiv-postcomp-is-emb H {l3} = equiv-postcomp-is-mono l3 f (is-mono-is-emb H)

equiv-postcomp-emb :
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A ↪ B) (g h : X → A) →
  (g ＝ h) ≃ (map-emb f ∘ g ＝ map-emb f ∘ h)
equiv-postcomp-emb (f , H) = equiv-postcomp-is-emb f H
```

We construct an explicit equivalence for postcomposition for homotopies between
functions (rather than equality) when the map is an embedding.

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} (f : A ↪ B)
  {X : UU l3} (g h : X → A)
  where

  map-inv-equiv-htpy-postcomp-emb :
    map-emb f ∘ g ~ map-emb f ∘ h → g ~ h
  map-inv-equiv-htpy-postcomp-emb H x =
    map-inv-is-equiv (is-emb-map-emb f (g x) (h x)) (H x)

  is-section-map-inv-equiv-htpy-postcomp-emb :
    is-section
      ( left-whisker-comp (map-emb f))
      ( map-inv-equiv-htpy-postcomp-emb)
  is-section-map-inv-equiv-htpy-postcomp-emb H =
    eq-htpy
      ( λ x → is-section-map-inv-is-equiv (is-emb-map-emb f (g x) (h x)) (H x))

  is-retraction-map-inv-equiv-htpy-postcomp-emb :
    is-retraction
      ( left-whisker-comp (map-emb f))
      ( map-inv-equiv-htpy-postcomp-emb)
  is-retraction-map-inv-equiv-htpy-postcomp-emb H =
    eq-htpy
      ( λ x →
        is-retraction-map-inv-is-equiv (is-emb-map-emb f (g x) (h x)) (H x))

  is-equiv-left-whisker-emb :
    is-equiv (left-whisker-comp (map-emb f) {g} {h})
  is-equiv-left-whisker-emb =
    is-equiv-is-invertible
      map-inv-equiv-htpy-postcomp-emb
      is-section-map-inv-equiv-htpy-postcomp-emb
      is-retraction-map-inv-equiv-htpy-postcomp-emb

  equiv-htpy-postcomp-emb :
    (g ~ h) ≃ (map-emb f ∘ g ~ map-emb f ∘ h)
  equiv-htpy-postcomp-emb =
    ( left-whisker-comp (map-emb f) , is-equiv-left-whisker-emb)
```

### Smallness of the mono predicate

In order to avoid cyclic dependencies, we need to type out the definition of
being small.

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-small-lzero-is-mono :
    {l3 : Level} → Σ (UU (lsuc lzero ⊔ l1 ⊔ l2)) (λ P → is-mono l3 f ≃ P)
  is-small-lzero-is-mono {l3} =
    ( is-mono lzero f ,
      equiv-iff (is-mono-Prop l3 f) (is-mono-Prop lzero f) (λ X H → {! i  !}) {!   !})
```
