# Codiagonals of maps

```agda
module synthetic-homotopy-theory.codiagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **codiagonal** of a map `f : A → B` is the unique map `∇ f : B ⊔_A B → B`
equipped with [homotopies](foundation-core.homotopies.md)

```text
  H : ∇ f ∘ inl ~ id
  K : ∇ f ∘ inr ~ id
  L : (H ·r f) ~ (∇ f ·l glue) ∙h (K ·r f)
```

The [fibers](foundation-core.fibers-of-maps.md) of the codiagonal are equivalent
to the [suspensions](synthetic-homotopy-theory.suspensions-of-types.md) of the
fibers of `f`.

## Definitions

### The codiagonal of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  cocone-codiagonal-map : cocone f f B
  pr1 cocone-codiagonal-map = id
  pr1 (pr2 cocone-codiagonal-map) = id
  pr2 (pr2 cocone-codiagonal-map) = refl-htpy

  codiagonal-map : pushout f f → B
  codiagonal-map = cogap f f cocone-codiagonal-map

  compute-inl-codiagonal-map :
    codiagonal-map ∘ inl-pushout f f ~ id
  compute-inl-codiagonal-map =
    compute-inl-cogap f f cocone-codiagonal-map

  compute-inr-codiagonal-map :
    codiagonal-map ∘ inr-pushout f f ~ id
  compute-inr-codiagonal-map =
    compute-inr-cogap f f cocone-codiagonal-map

  compute-glue-codiagonal-map :
    statement-coherence-htpy-cocone f f
      ( cocone-map f f (cocone-pushout f f) codiagonal-map)
      ( cocone-codiagonal-map)
      ( compute-inl-codiagonal-map)
      ( compute-inr-codiagonal-map)
  compute-glue-codiagonal-map =
    compute-glue-cogap f f cocone-codiagonal-map
```

## Properties

### The codiagonal is the fiberwise suspension

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  universal-property-suspension-cocone-fiber :
    {l : Level} →
    Σ ( cocone
        ( terminal-map (fiber f b))
        ( terminal-map (fiber f b))
        ( fiber (codiagonal-map f) b))
      ( universal-property-pushout-Level l
        ( terminal-map (fiber f b))
        ( terminal-map (fiber f b)))
  universal-property-suspension-cocone-fiber =
    universal-property-pushout-cogap-fiber-up-to-equiv f f
      ( cocone-codiagonal-map f)
      ( b)
      ( fiber f b)
      ( unit)
      ( unit)
      ( inv-equiv (equiv-unit-is-contr (is-torsorial-Id' b)))
      ( inv-equiv (equiv-unit-is-contr (is-torsorial-Id' b)))
      ( id-equiv)
      ( terminal-map (fiber f b))
      ( terminal-map (fiber f b))
      ( λ _ → eq-is-contr (is-torsorial-Id' b))
      ( λ _ → eq-is-contr (is-torsorial-Id' b))

  suspension-cocone-fiber :
    suspension-cocone (fiber f b) (fiber (codiagonal-map f) b)
  suspension-cocone-fiber =
    pr1 (universal-property-suspension-cocone-fiber {lzero})

  universal-property-suspension-fiber :
    universal-property-pushout
      ( terminal-map (fiber f b))
      ( terminal-map (fiber f b))
      ( suspension-cocone-fiber)
  universal-property-suspension-fiber =
    pr2 universal-property-suspension-cocone-fiber

  fiber-codiagonal-map-suspension-fiber :
    suspension (fiber f b) → fiber (codiagonal-map f) b
  fiber-codiagonal-map-suspension-fiber =
    cogap-suspension' suspension-cocone-fiber

  is-equiv-fiber-codiagonal-map-suspension-fiber :
    is-equiv fiber-codiagonal-map-suspension-fiber
  is-equiv-fiber-codiagonal-map-suspension-fiber =
    is-equiv-up-pushout-up-pushout
      ( terminal-map (fiber f b))
      ( terminal-map (fiber f b))
      ( cocone-suspension (fiber f b))
      ( suspension-cocone-fiber)
      ( cogap-suspension' (suspension-cocone-fiber))
      ( htpy-cocone-map-universal-property-pushout
        ( terminal-map (fiber f b))
        ( terminal-map (fiber f b))
        ( cocone-suspension (fiber f b))
        ( up-suspension' (fiber f b))
        ( suspension-cocone-fiber))
      ( up-suspension' (fiber f b))
      ( universal-property-suspension-fiber)

  equiv-fiber-codiagonal-map-suspension-fiber :
    suspension (fiber f b) ≃ fiber (codiagonal-map f) b
  pr1 equiv-fiber-codiagonal-map-suspension-fiber =
    fiber-codiagonal-map-suspension-fiber
  pr2 equiv-fiber-codiagonal-map-suspension-fiber =
    is-equiv-fiber-codiagonal-map-suspension-fiber
```
