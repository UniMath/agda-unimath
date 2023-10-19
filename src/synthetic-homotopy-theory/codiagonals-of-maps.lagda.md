# Codiagonals of maps

```agda
module synthetic-homotopy-theory.codiagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.functoriality-dependent-pair-types

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.unit-type

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.suspension-structures
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

### The codiagonal is the fiberwise suspension

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  private
    P : pushout f f → UU l2
    P x = codiagonal-map f x ＝ b

    c : cocone f f (pushout f f)
    c = cocone-pushout f f

  pushout-1 : {l : Level} →
                universal-property-pushout l
                (vertical-map-span-flattening-pushout P f f c)
                (horizontal-map-span-flattening-pushout P f f c)
                (cocone-flattening-pushout P f f c)
  pushout-1 =
    flattening-lemma-pushout P f f
      ( c)
      ( dependent-up-pushout f f)

  note-1 : Σ A (P ∘ inl-pushout f f ∘ f) →
           Σ B (P ∘ inr-pushout f f)
  note-1 = horizontal-map-span-flattening-pushout P f f c

  bottom-right : UU (l1 ⊔ l2)
  bottom-right = fiber (codiagonal-map f) b

  correct-cocone' : cocone (vertical-map-span-flattening-pushout P f f c) (horizontal-map-span-flattening-pushout P f f c) bottom-right
  correct-cocone' = cocone-flattening-pushout P f f c

  bottom-left : UU l2
  bottom-left = Σ B (λ y → P (inl-pushout f f y))

  top-right : UU l2
  top-right = Σ B (λ y → P (inr-pushout f f y))

  top-left : UU (l1 ⊔ l2)
  top-left = Σ A (λ a → P (inl-pushout f f (f a)))

  horizontal-span : top-left → top-right
  horizontal-span = horizontal-map-span-flattening-pushout P f f c

  horizontal-cocone : bottom-left → bottom-right
  horizontal-cocone = horizontal-map-cocone-flattening-pushout P f f c

  equiv-top-left : fiber f b ≃ top-left
  equiv-top-left = equiv-tot (λ a → equiv-concat (compute-inl-codiagonal-map f (f a)) b)

  equiv-top-right : unit ≃ top-right
  equiv-top-right = {!!} {- terminal-map , (is-equiv-terminal-map-is-contr (is-contr-equiv (Σ B (λ y → y ＝ b)) (equiv-tot (λ y → equiv-concat (compute-inr-codiagonal-map f y)) b) (is-contr-total-path' b))) -}

  equiv-bottom-left : unit ≃ bottom-left
  equiv-bottom-left = {!!}
  {- terminal-map , (is-equiv-terminal-map-is-contr (is-contr-equiv (Σ B (λ y → y ＝ b)) (equiv-tot (λ y → equiv-concat (inv (compute-inl-codiagonal-map f y)) b)) (is-contr-total-path' b))) -}

  coh : fiber f b →
        (inl-pushout f f b , compute-inl-codiagonal-map f b) ＝
        (inr-pushout f f b , compute-inr-codiagonal-map f b)
  coh (a , p) = {!!}

  suspension-structure-fiber : suspension-structure (fiber f b) (Σ (pushout f f) P)
  suspension-structure-fiber =
    ((inl-pushout f f b , compute-inl-codiagonal-map f b) ,
    (inr-pushout f f b , compute-inr-codiagonal-map f b) ,
    {!!})

  pushout-2 : {l : Level} →
    universal-property-pushout l
      terminal-map
      terminal-map
      {!!}
  pushout-2 =
    universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv
      ( vertical-map-span-flattening-pushout P f f c)
      ( horizontal-map-span-flattening-pushout P f f c)
      ( horizontal-map-cocone-flattening-pushout P f f c)
      ( vertical-map-cocone-flattening-pushout P f f c)
      ( terminal-map)
      ( terminal-map)
      ( point (inl-pushout f f b , compute-inl-codiagonal-map f b))
      ( point (inr-pushout f f b , compute-inr-codiagonal-map f b))
      ( map-equiv equiv-top-left)
      ( map-equiv equiv-bottom-left)
      ( map-equiv equiv-top-right)
      ( id)
      {!!}
      {!!}
      {!!}
      {!!}
      {!!}
      {!!}
      {!!}
      ( is-equiv-map-equiv equiv-top-left)
      ( is-equiv-map-equiv equiv-bottom-left)
      ( is-equiv-map-equiv equiv-top-right)
      ( is-equiv-id)
      pushout-1

--  bottom-right-equiv : bottom-right ≃
--  bottom-right-equiv = {!equiv-tot!}
```
