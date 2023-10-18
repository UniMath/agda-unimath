# Epimorphisms

```agda
module foundation.epimorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.propositional-maps
open import foundation.sections
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
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
    A → B
  f ↓   ↓ id
    B → B
      id
```

is a pushout square.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (X : UU l3)
  where

  equiv-fibers-precomp-cocone :
    Σ (B → X) (λ g → fiber (precomp f X) (g ∘ f)) ≃ cocone f f X
  equiv-fibers-precomp-cocone =
    equiv-tot ( λ g →
                ( equiv-tot (λ h → equiv-funext) ∘e
                ( equiv-fiber (precomp f X) (g ∘ f))))

  diagonal-into-fibers-precomp :
    (B → X) → Σ (B → X) (λ g → fiber (precomp f X) (g ∘ f))
  diagonal-into-fibers-precomp = map-section-family (λ g → g , refl)

  is-equiv-diagonal-into-fibers-precomp-is-epimorphism :
    is-epimorphism f → is-equiv diagonal-into-fibers-precomp
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
    {l : Level} → universal-property-pushout l f f (cocone-codiagonal-map f)
  universal-property-pushout-is-epimorphism e X =
    is-equiv-comp
      ( map-equiv (equiv-fibers-precomp-cocone f X))
      ( diagonal-into-fibers-precomp f X)
      ( is-equiv-diagonal-into-fibers-precomp-is-epimorphism f X e)
      ( is-equiv-map-equiv (equiv-fibers-precomp-cocone f X))
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

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
