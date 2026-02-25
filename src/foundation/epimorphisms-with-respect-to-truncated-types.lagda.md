# Epimorphisms with respect to truncated types

```agda
module foundation.epimorphisms-with-respect-to-truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-extensionality
open import foundation.functoriality-truncation
open import foundation.precomposition-functions
open import foundation.sections
open import foundation.truncation-equivalences
open import foundation.truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

A map `f : A → B` is said to be a **`k`-epimorphism** if the precomposition
function

```text
  - ∘ f : (B → X) → (A → X)
```

is an embedding for every `k`-truncated type `X`.

## Definitions

### `k`-epimorphisms

```agda
is-epimorphism-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (A → B) → UUω
is-epimorphism-Truncated-Type k f =
  {l : Level} (X : Truncated-Type l k) →
  is-emb (precomp f (type-Truncated-Type X))
```

## Properties

### Every `k+1`-epimorphism is a `k`-epimorphism

```agda
is-epimorphism-is-epimorphism-succ-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-epimorphism-Truncated-Type (succ-𝕋 k) f →
  is-epimorphism-Truncated-Type k f
is-epimorphism-is-epimorphism-succ-Truncated-Type k f H X =
  H (truncated-type-succ-Truncated-Type k X)
```

### Every map is a `-1`-epimorphism

```agda
is-neg-one-epimorphism :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-epimorphism-Truncated-Type neg-one-𝕋 f
is-neg-one-epimorphism f P =
  is-emb-is-prop
    ( is-prop-function-type (is-prop-type-Prop P))
    ( is-prop-function-type (is-prop-type-Prop P))
```

### Every `k`-equivalence is a `k`-epimorphism

```agda
is-epimorphism-is-truncation-equivalence-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-truncation-equivalence k f →
  is-epimorphism-Truncated-Type k f
is-epimorphism-is-truncation-equivalence-Truncated-Type k f H X =
  is-emb-is-equiv (is-equiv-precomp-is-truncation-equivalence H X)
```

### A map is a `k`-epimorphism if and only if its `k`-truncation is a `k`-epimorphism

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-epimorphism-is-epimorphism-map-trunc-Truncated-Type :
    is-epimorphism-Truncated-Type k (map-trunc k f) →
    is-epimorphism-Truncated-Type k f
  is-epimorphism-is-epimorphism-map-trunc-Truncated-Type H X =
    is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps
      ( precomp (map-trunc k f) (type-Truncated-Type X))
      ( precomp unit-trunc (type-Truncated-Type X))
      ( precomp unit-trunc (type-Truncated-Type X))
      ( precomp f (type-Truncated-Type X))
      ( precomp-coherence-square-maps
        ( unit-trunc)
        ( f)
        ( map-trunc k f)
        ( unit-trunc)
        ( inv-htpy (coherence-square-map-trunc k f))
        ( type-Truncated-Type X))
      ( is-truncation-trunc X)
      ( is-truncation-trunc X)
      ( H X)

  is-epimorphism-map-trunc-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    is-epimorphism-Truncated-Type k (map-trunc k f)
  is-epimorphism-map-trunc-is-epimorphism-Truncated-Type H X =
    is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps
      ( precomp (map-trunc k f) (type-Truncated-Type X))
      ( precomp unit-trunc (type-Truncated-Type X))
      ( precomp unit-trunc (type-Truncated-Type X))
      ( precomp f (type-Truncated-Type X))
      ( precomp-coherence-square-maps
        ( unit-trunc)
        ( f)
        ( map-trunc k f)
        ( unit-trunc)
        ( inv-htpy (coherence-square-map-trunc k f))
        ( type-Truncated-Type X))
      ( is-truncation-trunc X)
      ( is-truncation-trunc X)
      ( H X)
```

### The class of `k`-epimorphisms is closed under composition and has the right cancellation property

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B)
  where

  is-epimorphism-comp-Truncated-Type :
    is-epimorphism-Truncated-Type k g →
    is-epimorphism-Truncated-Type k f →
    is-epimorphism-Truncated-Type k (g ∘ f)
  is-epimorphism-comp-Truncated-Type eg ef X =
    is-emb-comp
      ( precomp f (type-Truncated-Type X))
      ( precomp g (type-Truncated-Type X))
      ( ef X)
      ( eg X)

  is-epimorphism-left-factor-Truncated-Type :
    is-epimorphism-Truncated-Type k (g ∘ f) →
    is-epimorphism-Truncated-Type k f →
    is-epimorphism-Truncated-Type k g
  is-epimorphism-left-factor-Truncated-Type ec ef X =
    is-emb-right-factor
      ( precomp f (type-Truncated-Type X))
      ( precomp g (type-Truncated-Type X))
      ( ef X)
      ( ec X)
```

### A map `f` is a `k`-epimorphism if and only if the horizontal/vertical projections from `cocone {X} f f` are equivalences for all `k`-types `X`

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-equiv-diagonal-into-fibers-precomp-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (diagonal-into-fibers-precomp f)
  is-equiv-diagonal-into-fibers-precomp-is-epimorphism-Truncated-Type e X =
    is-equiv-map-section-family
      ( λ g → g , refl)
      ( λ g →
        is-proof-irrelevant-is-prop
          ( is-prop-map-is-emb (e X) (g ∘ f))
          ( g , refl))

  is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (diagonal-into-cocone f (type-Truncated-Type X))
  is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Type e X =
    is-equiv-comp
      ( map-equiv (compute-total-fiber-precomp f))
      ( diagonal-into-fibers-precomp f)
      ( is-equiv-diagonal-into-fibers-precomp-is-epimorphism-Truncated-Type e X)
      ( is-equiv-map-equiv (compute-total-fiber-precomp f))

  is-equiv-horizontal-map-cocone-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (horizontal-map-cocone {X = type-Truncated-Type X} f f)
  is-equiv-horizontal-map-cocone-is-epimorphism-Truncated-Type e X =
    is-equiv-left-factor
      ( horizontal-map-cocone f f)
      ( diagonal-into-cocone f (type-Truncated-Type X))
      ( is-equiv-id)
      ( is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Type e X)

  is-equiv-vertical-map-cocone-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (vertical-map-cocone {X = type-Truncated-Type X} f f)
  is-equiv-vertical-map-cocone-is-epimorphism-Truncated-Type e X =
    is-equiv-left-factor
      ( vertical-map-cocone f f)
      ( diagonal-into-cocone f (type-Truncated-Type X))
      ( is-equiv-id)
      ( is-equiv-diagonal-into-cocone-is-epimorphism-Truncated-Type e X)

  is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Type :
    ( {l : Level} (X : Truncated-Type l k) →
      is-equiv (horizontal-map-cocone {X = type-Truncated-Type X} f f)) →
    is-epimorphism-Truncated-Type k f
  is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Type h X =
    is-emb-is-contr-fibers-values
      ( precomp f (type-Truncated-Type X))
      ( λ g →
        is-contr-equiv
          ( Σ ( B → (type-Truncated-Type X))
              ( λ h → coherence-square-maps f f h g))
          ( compute-fiber-precomp f g)
          ( is-contr-is-equiv-pr1 (h X) g))

  is-epimorphism-is-equiv-vertical-map-cocone-Truncated-Type :
    ( {l : Level} (X : Truncated-Type l k) →
      is-equiv (vertical-map-cocone {X = type-Truncated-Type X} f f)) →
    is-epimorphism-Truncated-Type k f
  is-epimorphism-is-equiv-vertical-map-cocone-Truncated-Type h =
    is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Type
      ( λ X →
        is-equiv-comp
          ( vertical-map-cocone f f)
          ( swap-cocone f f (type-Truncated-Type X))
          ( is-equiv-swap-cocone f f (type-Truncated-Type X))
          ( h X))
```

### The codiagonal of a `k`-epimorphism is a `k`-equivalence

We consider the commutative diagram for any `k`-type `X`:

```text
              horizontal-map-cocone
  (B → X) <---------------------------- cocone f f X
     |                  ≃                  ∧
  id | ≃                                 ≃ | (universal property)
     ∨                                     |
  (B → X) ------------------------> (pushout f f → X)
           precomp (codiagonal f)
```

Since the top (in case `f` is epic), left and right maps are all equivalences,
so is the bottom map.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncation-equivalence-codiagonal-map-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    is-truncation-equivalence k (codiagonal-map f)
  is-truncation-equivalence-codiagonal-map-is-epimorphism-Truncated-Type e =
    is-truncation-equivalence-is-equiv-precomp
      ( λ l X →
        is-equiv-right-factor
          ( ( horizontal-map-cocone f f) ∘
            ( map-equiv (equiv-up-pushout f f (type-Truncated-Type X))))
          ( precomp (codiagonal-map f) (type-Truncated-Type X))
          ( is-equiv-comp
            ( horizontal-map-cocone f f)
            ( map-equiv (equiv-up-pushout f f (type-Truncated-Type X)))
            ( is-equiv-map-equiv (equiv-up-pushout f f (type-Truncated-Type X)))
            ( is-equiv-horizontal-map-cocone-is-epimorphism-Truncated-Type
              ( k)
              ( f)
              ( e)
              ( X)))
          ( is-equiv-htpy-id
            ( λ g → eq-htpy (λ b → ap g (compute-inl-codiagonal-map f b)))))
```

### A map is a `k`-epimorphism if its codiagonal is a `k`-equivalence

We use the same diagram as above.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-equiv-horizontal-map-cocone-is-truncation-equivalence-codiagonal-map :
    is-truncation-equivalence k (codiagonal-map f) →
    {l : Level} (X : Truncated-Type l k) →
    is-equiv (horizontal-map-cocone {X = type-Truncated-Type X} f f)
  is-equiv-horizontal-map-cocone-is-truncation-equivalence-codiagonal-map e X =
    is-equiv-left-factor
      ( horizontal-map-cocone f f)
      ( ( map-equiv (equiv-up-pushout f f (type-Truncated-Type X))) ∘
        ( precomp (codiagonal-map f) (type-Truncated-Type X)))
      ( is-equiv-htpy-id
        ( λ g → eq-htpy (λ b → ap g (compute-inl-codiagonal-map f b))))
      ( is-equiv-comp
        ( map-equiv (equiv-up-pushout f f (type-Truncated-Type X)))
        ( precomp (codiagonal-map f) (type-Truncated-Type X))
        (is-equiv-precomp-is-truncation-equivalence e X)
        ( is-equiv-map-equiv (equiv-up-pushout f f (type-Truncated-Type X))))

  is-epimorphism-is-truncation-equivalence-codiagonal-map-Truncated-Type :
    is-truncation-equivalence k (codiagonal-map f) →
    is-epimorphism-Truncated-Type k f
  is-epimorphism-is-truncation-equivalence-codiagonal-map-Truncated-Type e =
    is-epimorphism-is-equiv-horizontal-map-cocone-Truncated-Type k f
      ( is-equiv-horizontal-map-cocone-is-truncation-equivalence-codiagonal-map
        ( e))
```

### A map is a `k`-epimorphism if and only if its codiagonal is `k`-connected

This strengthens the above result about the codiagonal being a `k`-equivalence.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-epimorphism-is-connected-codiagonal-map-Truncated-Type :
    is-connected-map k (codiagonal-map f) → is-epimorphism-Truncated-Type k f
  is-epimorphism-is-connected-codiagonal-map-Truncated-Type c =
    is-epimorphism-is-truncation-equivalence-codiagonal-map-Truncated-Type k f
      ( is-truncation-equivalence-is-connected-map (codiagonal-map f) c)

  is-connected-codiagonal-map-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f → is-connected-map k (codiagonal-map f)
  is-connected-codiagonal-map-is-epimorphism-Truncated-Type e =
    is-connected-map-is-truncation-equivalence-section
      ( codiagonal-map f)
      ( k)
      ( inl-pushout f f , compute-inl-codiagonal-map f)
      ( is-truncation-equivalence-codiagonal-map-is-epimorphism-Truncated-Type
        ( k)
        ( f)
        ( e))
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
