# Codiagonals of maps

```agda
module synthetic-homotopy-theory.codiagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels
open import foundation.unit-type

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-suspensions
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

### Properties

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

--  fiber (horizontal-map-cocone f f (cocone-codiagonal-map f)) b
  test : fiber (horizontal-map-cocone f f (cocone-codiagonal-map f)) b ≃ fiber id b
  test = id , {!id-is-equiv!}

  suspension-cocone-fiber : suspension-cocone (fiber f b) (fiber (codiagonal-map f) b)
  suspension-cocone-fiber = pr1 (
    universal-property-pushout-cogap-fiber-up-to-equiv
     f
     f
     (cocone-codiagonal-map f)
     b
     (fiber f b)
     unit
     unit
     (inv-equiv (terminal-map , (is-equiv-terminal-map-is-contr (is-torsorial-path' b))))
     (inv-equiv (terminal-map , (is-equiv-terminal-map-is-contr (is-torsorial-path' b))))
     (id , is-equiv-id)
     terminal-map
     terminal-map
     (λ x → {!!})
     (λ x → {!!}))

  suspension-structure-fiber' : suspension-structure (fiber f b) (fiber (codiagonal-map f) b)
  suspension-structure-fiber' = {!!} {-
    map-equiv
     ( equiv-suspension-structure-suspension-cocone
       ( fiber f b)
       ( fiber (codiagonal-map f) b))
     ( suspension-cocone-fiber) -}

  is-suspension-fiber :
    {l : Level} →
    is-suspension l (fiber f b) (fiber (codiagonal-map f) b)
  is-suspension-fiber = {!!}

  {-
  universal-property-suspension-fiber' :
    {l : Level} →
    universal-property-suspension' l
      ( fiber f b)
      ( fiber (codiagonal-map f) b)
      ( suspension-structure-fiber)
  universal-property-suspension-fiber' = pushout-5 -}


  universal-property-suspension-fiber :
    {l : Level} →
    universal-property-pushout l
      ( terminal-map)
      ( terminal-map)
      ( suspension-cocone-fiber)
  universal-property-suspension-fiber {l} = {!!}

  suspension-fiber-is-fiber-codiagonal-map :
    suspension (fiber f b) ≃ fiber (codiagonal-map f) b
  suspension-fiber-is-fiber-codiagonal-map =
    ( cogap terminal-map terminal-map suspension-cocone-fiber ,
      is-equiv-up-pushout-up-pushout
        ( terminal-map)
        ( terminal-map)
        ( cocone-pushout terminal-map terminal-map)
        ( suspension-cocone-fiber)
        ( cogap terminal-map terminal-map (suspension-cocone-fiber))
        ( htpy-cocone-map-universal-property-pushout
          ( terminal-map)
          ( terminal-map)
          ( cocone-pushout terminal-map terminal-map)
          ( up-pushout terminal-map terminal-map)
          ( suspension-cocone-fiber))
        ( up-pushout terminal-map terminal-map)
        ( universal-property-suspension-fiber))
```
