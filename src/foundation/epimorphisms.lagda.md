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

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-epimorphism-level : (l : Level) → (A → B) → UU (l1 ⊔ l2 ⊔ lsuc l)
  is-epimorphism-level l f = (X : UU l) → is-emb (precomp f X)

  is-epimorphism : (A → B) → UUω
  is-epimorphism f = {l : Level} → is-epimorphism-level l f
```

## Properties

### Epimorphisms, pushouts and codiagonals


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

  equiv-fibers-of-precomp-cocone :
    Σ (B → X) (λ g → fiber (precomp f X) (g ∘ f)) ≃ cocone f f X
  equiv-fibers-of-precomp-cocone =
    equiv-comp
      ( equiv-Σ _
          ( id-equiv)
          ( λ g → equiv-Σ _ id-equiv (λ h → equiv-funext)))
      ( equiv-Σ _
          ( id-equiv)
          ( λ g → equiv-fiber (precomp f X) (g ∘ f)))

  diagonal-into-fibers-of-precomp :
    (B → X) → Σ (B → X) (λ g → fiber (precomp f X) (g ∘ f))
  diagonal-into-fibers-of-precomp = map-section-family (λ g → g , refl)

  is-equiv-diagonal-into-fibers-of-precomp-is-epimorphism :
    is-epimorphism f → is-equiv diagonal-into-fibers-of-precomp
  is-equiv-diagonal-into-fibers-of-precomp-is-epimorphism e =
    is-equiv-map-section-family
      ( λ g → g , refl)
      ( λ g → is-proof-irrelevant-is-prop
                ( is-prop-map-is-emb (e X) (g ∘ f))
                ( g , refl))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-pushout-is-epimorphism :
    is-epimorphism f →
    {l : Level} → universal-property-pushout l f f (cocone-codiagonal-map f)
  is-pushout-is-epimorphism e X =
    is-equiv-comp-htpy
      ( cocone-map f f (cocone-codiagonal-map f))
      ( map-equiv (equiv-fibers-of-precomp-cocone f X))
      ( diagonal-into-fibers-of-precomp f X)
      ( refl-htpy)
      ( is-equiv-diagonal-into-fibers-of-precomp-is-epimorphism f X e)
      ( is-equiv-map-equiv (equiv-fibers-of-precomp-cocone f X))
```

If the map `f : A → B` is epi, then its codiagonal is an equivalence.

```agda
  codiagonal-is-equiv-is-epimorphism :
    is-epimorphism f → is-equiv (codiagonal-map f)
  codiagonal-is-equiv-is-epimorphism e =
    is-equiv-up-pushout-up-pushout f f
      ( cocone-pushout f f)
      ( cocone-codiagonal-map f)
      ( codiagonal-map f)
      ( compute-inl-codiagonal-map f ,
        compute-inr-codiagonal-map f ,
        compute-glue-codiagonal-map f)
      ( up-pushout f f)
      ( is-pushout-is-epimorphism e)
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
