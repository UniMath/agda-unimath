# Quasiidempotent maps

```agda
module foundation.quasiidempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.homotopy-algebra
open import foundation.preidempotent-maps
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sets
```

</details>

## Idea

A {{#concept "quasiidempotent map" Agda=is-quasiidempotent-map}} is a map
`f : A → A` [equipped](foundation.structure.md) with a
[homotopy](foundation-core.homotopies.md) `I : f ∘ f ~ f` and a coherence

```text
  f ·l I ~ I ·r f.
```

While this data is not enough to capture a fully coherent idempotent map, it is
sufficient for showing that `f` can be made to be fully coherent. This is in
contrast to [preidempotent maps](foundation.preidempotent-maps.md), which may in
general fail to be coherent.

## Definitions

### The structure of quasiidempotence on maps

```agda
coherence-is-quasiidempotent-map :
  {l : Level} {A : UU l} (f : A → A) → f ∘ f ~ f → UU l
coherence-is-quasiidempotent-map f I = f ·l I ~ I ·r f

is-quasiidempotent-map : {l : Level} {A : UU l} → (A → A) → UU l
is-quasiidempotent-map f = Σ (f ∘ f ~ f) (coherence-is-quasiidempotent-map f)

module _
  {l : Level} {A : UU l} {f : A → A} (H : is-quasiidempotent-map f)
  where

  is-preidempotent-is-quasiidempotent-map : is-preidempotent-map f
  is-preidempotent-is-quasiidempotent-map = pr1 H

  coh-is-quasiidempotent-map :
    coherence-is-quasiidempotent-map f is-preidempotent-is-quasiidempotent-map
  coh-is-quasiidempotent-map = pr2 H
```

### The type of quasiidempotent maps

```agda
quasiidempotent-map : {l : Level} (A : UU l) → UU l
quasiidempotent-map A = Σ (A → A) (is-quasiidempotent-map)

module _
  {l : Level} {A : UU l} (H : quasiidempotent-map A)
  where

  map-quasiidempotent-map : A → A
  map-quasiidempotent-map = pr1 H

  is-quasiidempotent-quasiidempotent-map :
    is-quasiidempotent-map map-quasiidempotent-map
  is-quasiidempotent-quasiidempotent-map = pr2 H

  is-preidempotent-quasiidempotent-map :
    is-preidempotent-map map-quasiidempotent-map
  is-preidempotent-quasiidempotent-map =
    is-preidempotent-is-quasiidempotent-map
      ( is-quasiidempotent-quasiidempotent-map)

  coh-quasiidempotent-map :
    coherence-is-quasiidempotent-map
      ( map-quasiidempotent-map)
      ( is-preidempotent-quasiidempotent-map)
  coh-quasiidempotent-map =
    coh-is-quasiidempotent-map is-quasiidempotent-quasiidempotent-map

  preidempotent-map-quasiidempotent-map : preidempotent-map A
  preidempotent-map-quasiidempotent-map =
    ( map-quasiidempotent-map , is-preidempotent-quasiidempotent-map)
```

## Properties

### Being quasiidempotent on a set is a property

```agda
module _
  {l : Level} {A : UU l} (is-set-A : is-set A) (f : A → A)
  where

  is-prop-coherence-is-quasiidempotent-map-is-set :
    (I : f ∘ f ~ f) → is-prop (coherence-is-quasiidempotent-map f I)
  is-prop-coherence-is-quasiidempotent-map-is-set I =
    is-prop-Π
      ( λ x →
        is-set-is-prop
          ( is-set-A ((f ∘ f ∘ f) x) ((f ∘ f) x))
          ( (f ·l I) x)
          ( (I ·r f) x))

  is-prop-is-quasiidempotent-map-is-set : is-prop (is-quasiidempotent-map f)
  is-prop-is-quasiidempotent-map-is-set =
    is-prop-Σ
      ( is-prop-is-preidempotent-map-is-set is-set-A f)
      ( is-prop-coherence-is-quasiidempotent-map-is-set)

  is-quasiidempotent-map-is-set-Prop : Prop l
  is-quasiidempotent-map-is-set-Prop =
    ( is-quasiidempotent-map f , is-prop-is-quasiidempotent-map-is-set)

module _
  {l : Level} (A : Set l) (f : type-Set A → type-Set A)
  where

  is-prop-is-quasiidempotent-map-Set : is-prop (is-quasiidempotent-map f)
  is-prop-is-quasiidempotent-map-Set =
    is-prop-is-quasiidempotent-map-is-set (is-set-type-Set A) f

  is-quasiidempotent-map-prop-Set : Prop l
  is-quasiidempotent-map-prop-Set =
    ( is-quasiidempotent-map f , is-prop-is-quasiidempotent-map-Set)
```

### If `i` and `r` is an inclusion-retraction pair, then `i ∘ r` is quasiidempotent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (i : B → A) (r : A → B) (H : is-retraction i r)
  where

  coherence-is-quasiidempotent-inclusion-retraction :
    coherence-is-quasiidempotent-map (i ∘ r)
      ( is-preidempotent-inclusion-retraction i r H)
  coherence-is-quasiidempotent-inclusion-retraction =
    ( inv-preserves-comp-left-whisker-comp i r (i ·l H ·r r)) ∙h
    ( double-whisker-comp²
      ( i)
      ( preserves-comp-left-whisker-comp r i H ∙h inv-coh-htpy-id H)
      ( r))

  is-quasiidempotent-inclusion-retraction : is-quasiidempotent-map (i ∘ r)
  is-quasiidempotent-inclusion-retraction =
    ( is-preidempotent-inclusion-retraction i r H ,
      coherence-is-quasiidempotent-inclusion-retraction)
```

### Quasiidempotence is preserved by homotopies

```agda
module _
  {l : Level} {A : UU l} {f g : A → A} (F : is-quasiidempotent-map f)
  where

  abstract
    coherence-is-quasiidempotent-map-htpy :
      (H : g ~ f) →
      coherence-is-quasiidempotent-map g
        ( is-preidempotent-map-htpy
          ( is-preidempotent-is-quasiidempotent-map F)
          ( H))
    coherence-is-quasiidempotent-map-htpy H =
      ( right-transpose-htpy-concat
        ( g ·l
          is-preidempotent-map-htpy
            ( is-preidempotent-is-quasiidempotent-map F)
            ( H))
        ( H ·r g)
        ( H ·r (g ∘ g) ∙h
          ( ( f) ·l
            ( g ·l H ∙h
              H ·r f ∙h
              is-preidempotent-is-quasiidempotent-map F ∙h inv-htpy H)))
        ( inv-htpy
          ( ( nat-htpy H) ∘
            ( g ·l H ∙h
              H ·r f ∙h
              is-preidempotent-is-quasiidempotent-map F ∙h
              inv-htpy H)))) ∙h
      ( ap-concat-htpy'
        ( inv-htpy (H ·r g))
        ( ( ap-concat-htpy
            ( H ·r ((g ∘ g)))
            ( ( distributive-left-whisker-comp-concat f
                ( g ·l H ∙h H ·r f ∙h is-preidempotent-is-quasiidempotent-map F)
                ( inv-htpy H)) ∙h
              ( ap-concat-htpy'
                ( f ·l inv-htpy H)
                ( ( distributive-left-whisker-comp-concat f
                    ( g ·l H ∙h H ·r f)
                    ( is-preidempotent-is-quasiidempotent-map F)) ∙h
                  ( ap-binary-concat-htpy
                    ( distributive-left-whisker-comp-concat f
                      ( g ·l H)
                      ( H ·r f))
                    ( coh-is-quasiidempotent-map F)))) ∙h
              ( assoc-htpy
                ( f ·l g ·l H ∙h f ·l H ·r f)
                ( is-preidempotent-is-quasiidempotent-map F ·r f)
                ( f ·l inv-htpy H)) ∙h
              ( ap-concat-htpy
                ( f ·l g ·l H ∙h f ·l H ·r f)
                ( ( nat-htpy (is-preidempotent-is-quasiidempotent-map F)) ∘
                  ( inv-htpy H))) ∙h
              ( inv-htpy
                ( assoc-htpy
                  ( f ·l g ·l H ∙h f ·l H ·r f)
                  ( (f ∘ f) ·l inv-htpy H)
                  ( is-preidempotent-is-quasiidempotent-map F ·r g))))) ∙h
          ( inv-htpy
            ( assoc-htpy
              ( H ·r (g ∘ g))
              ( f ·l g ·l H ∙h f ·l H ·r f ∙h (f ∘ f) ·l inv-htpy H)
              ( is-preidempotent-is-quasiidempotent-map F ·r g))) ∙h
          ( ap-concat-htpy'
            ( is-preidempotent-is-quasiidempotent-map F ·r g)
            ( ( ap-concat-htpy
                ( H ·r (g ∘ g))
                ( ap-concat-htpy'
                  ( (f ∘ f) ·l inv-htpy H)
                  ( ( ap-concat-htpy'
                      ( f ·l H ·r f)
                      ( preserves-comp-left-whisker-comp f g H)) ∙h
                    ( inv-htpy (nat-htpy (f ·l H) ∘ H))) ∙h
                  ( ap-concat-htpy
                    ( f ·l H ·r g ∙h (f ∘ f) ·l H)
                    ( left-whisker-inv-htpy (f ∘ f) H)) ∙h
                  ( right-right-inv-htpy (f ·l H ·r g) ((f ∘ f) ·l H)))) ∙h
              ( nat-htpy H ∘ (H ·r g))))))

  is-quasiidempotent-map-htpy : g ~ f → is-quasiidempotent-map g
  pr1 (is-quasiidempotent-map-htpy H) =
    is-preidempotent-map-htpy
      ( is-preidempotent-is-quasiidempotent-map F)
      ( H)
  pr2 (is-quasiidempotent-map-htpy H) =
    coherence-is-quasiidempotent-map-htpy H

  is-quasiidempotent-map-inv-htpy : f ~ g → is-quasiidempotent-map g
  pr1 (is-quasiidempotent-map-inv-htpy H) =
    is-preidempotent-map-htpy
      ( is-preidempotent-is-quasiidempotent-map F)
      ( inv-htpy H)
  pr2 (is-quasiidempotent-map-inv-htpy H) =
    coherence-is-quasiidempotent-map-htpy (inv-htpy H)
```

### Realigning the quasiidempotence coherence

Given a quasiidempotent `f` then any other preidempotence homotopy
`H : f ∘ f ~ f` that is homotopic to the coherent one is also coherent.

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (F : is-quasiidempotent-map f)
  where

  coherence-is-quasiidempotent-is-preidempotent-map-htpy :
    (I : f ∘ f ~ f) → is-preidempotent-is-quasiidempotent-map F ~ I →
    coherence-is-quasiidempotent-map f I
  coherence-is-quasiidempotent-is-preidempotent-map-htpy I α =
    ( left-whisker-comp² f (inv-htpy α)) ∙h
    ( coh-is-quasiidempotent-map F) ∙h
    ( right-whisker-comp² α f)

  coherence-is-quasiidempotent-is-preidempotent-map-inv-htpy :
    (I : f ∘ f ~ f) → I ~ is-preidempotent-is-quasiidempotent-map F →
    coherence-is-quasiidempotent-map f I
  coherence-is-quasiidempotent-is-preidempotent-map-inv-htpy I α =
    ( left-whisker-comp² f α) ∙h
    ( coh-is-quasiidempotent-map F) ∙h
    ( right-whisker-comp² (inv-htpy α) f)

  is-quasiidempotent-is-preidempotent-map-htpy :
    (I : f ∘ f ~ f) → is-preidempotent-is-quasiidempotent-map F ~ I →
    is-quasiidempotent-map f
  is-quasiidempotent-is-preidempotent-map-htpy I α =
    ( I , coherence-is-quasiidempotent-is-preidempotent-map-htpy I α)

  is-quasiidempotent-is-preidempotent-map-inv-htpy :
    (I : f ∘ f ~ f) → I ~ is-preidempotent-is-quasiidempotent-map F →
    is-quasiidempotent-map f
  is-quasiidempotent-is-preidempotent-map-inv-htpy I α =
    ( I , coherence-is-quasiidempotent-is-preidempotent-map-inv-htpy I α)
```

## See also

- In [`foundation.split-idempotent-maps`](foundation.split-idempotent-maps.md)
  we show that every quasiidempotent splits. In fact, split idempotents are a
  retract of quasiidempotents.

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
