# Epimorphisms

```agda
module foundation.epimorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.precomposition-functions
open import foundation.sections
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

A map `f : A → B` is said to be an **epimorphism** if the precomposition
function

```text
  - ∘ f : (B → X) → (A → X)
```

is an [embedding](foundation-core.embeddings.md) for every type `X`.

## Definitions

### Epimorphisms with respect to a specified universe

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-epimorphism-Level : (l : Level) → (A → B) → UU (l1 ⊔ l2 ⊔ lsuc l)
  is-epimorphism-Level l f = (X : UU l) → is-emb (precomp f X)
```

### Epimorphisms

```agda
  is-epimorphism : (A → B) → UUω
  is-epimorphism f = {l : Level} → is-epimorphism-Level l f
```

## Properties

### The codiagonal of an epimorphism is an equivalence

If the map `f : A → B` is epi, then the commutative square

```text
        f
    A -----> B
    |        |
  f |        | id
    ∨      ⌜ ∨
    B -----> B
        id
```

is a pushout square.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (X : UU l3)
  where

  is-equiv-diagonal-into-fibers-precomp-is-epimorphism :
    is-epimorphism f → is-equiv (diagonal-into-fibers-precomp f)
  is-equiv-diagonal-into-fibers-precomp-is-epimorphism e =
    is-equiv-map-section-family
      ( λ g → (g , refl))
      ( λ g →
        is-proof-irrelevant-is-prop
          ( is-prop-map-is-emb (e X) (g ∘ f))
          ( g , refl))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  universal-property-pushout-is-epimorphism :
    is-epimorphism f →
    universal-property-pushout f f (cocone-codiagonal-map f)
  universal-property-pushout-is-epimorphism e X =
    is-equiv-comp
      ( map-equiv (compute-total-fiber-precomp f))
      ( diagonal-into-fibers-precomp f)
      ( is-equiv-diagonal-into-fibers-precomp-is-epimorphism f X e)
      ( is-equiv-map-equiv (compute-total-fiber-precomp f))
```

If the map `f : A → B` is epi, then its codiagonal is an equivalence.

```agda
  is-equiv-codiagonal-map-is-epimorphism :
    is-epimorphism f → is-equiv (codiagonal-map f)
  is-equiv-codiagonal-map-is-epimorphism e =
    is-equiv-up-pushout-up-pushout f f
      ( cocone-pushout f f)
      ( cocone-codiagonal-map f)
      ( codiagonal-map f)
      ( compute-inl-codiagonal-map f ,
        compute-inr-codiagonal-map f ,
        compute-glue-codiagonal-map f)
      ( up-pushout f f)
      ( universal-property-pushout-is-epimorphism e)

  is-pushout-is-epimorphism :
    is-epimorphism f → is-pushout f f (cocone-codiagonal-map f)
  is-pushout-is-epimorphism = is-equiv-codiagonal-map-is-epimorphism
```

### A map is an epimorphism if its codiagonal is an equivalence

```agda
  is-epimorphism-universal-property-pushout-Level :
    {l : Level} →
    universal-property-pushout-Level l f f (cocone-codiagonal-map f) →
    is-epimorphism-Level l f
  is-epimorphism-universal-property-pushout-Level up-c X =
    is-emb-is-contr-fibers-values
      ( precomp f X)
      ( λ g →
        is-contr-equiv
          ( Σ (B → X) (λ h → coherence-square-maps f f h g))
          ( compute-fiber-precomp f g)
          ( is-contr-fam-is-equiv-map-section-family
            ( λ h →
              ( vertical-map-cocone f f
                ( cocone-map f f (cocone-codiagonal-map f) h)) ,
              ( coherence-square-cocone f f
                ( cocone-map f f (cocone-codiagonal-map f) h)))
            ( up-c X)
            ( g)))

  is-epimorphism-universal-property-pushout :
    universal-property-pushout f f (cocone-codiagonal-map f) →
    is-epimorphism f
  is-epimorphism-universal-property-pushout up-c =
    is-epimorphism-universal-property-pushout-Level up-c

  is-epimorphism-is-equiv-codiagonal-map :
    is-equiv (codiagonal-map f) → is-epimorphism f
  is-epimorphism-is-equiv-codiagonal-map e =
    is-epimorphism-universal-property-pushout
      ( up-pushout-up-pushout-is-equiv f f
        ( cocone-pushout f f)
        ( cocone-codiagonal-map f)
        ( codiagonal-map f)
        ( htpy-cocone-map-universal-property-pushout f f
          ( cocone-pushout f f)
          ( up-pushout f f)
          ( cocone-codiagonal-map f))
        ( e)
        ( up-pushout f f))

  is-epimorphism-is-pushout :
    is-pushout f f (cocone-codiagonal-map f) → is-epimorphism f
  is-epimorphism-is-pushout = is-epimorphism-is-equiv-codiagonal-map
```

### The class of epimorphisms is closed under composition and has the right cancellation property

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B)
  where

  is-epimorphism-comp :
    is-epimorphism g → is-epimorphism f → is-epimorphism (g ∘ f)
  is-epimorphism-comp eg ef X =
    is-emb-comp (precomp f X) (precomp g X) (ef X) (eg X)

  is-epimorphism-left-factor :
    is-epimorphism (g ∘ f) → is-epimorphism f → is-epimorphism g
  is-epimorphism-left-factor ec ef X =
    is-emb-right-factor (precomp f X) (precomp g X) (ef X) (ec X)
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
