# Quasicoherently idempotent maps

```agda
module foundation.quasicoherently-idempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.homotopy-algebra
open import foundation.idempotent-maps
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

A
{{#concept "quasicoherently idempotent map" Agda=is-quasicoherently-idempotent-map}}
is a map `f : A → A` [equipped](foundation.structure.md) with a
[homotopy](foundation-core.homotopies.md) `I : f ∘ f ~ f` and a coherence

```text
  f ·l I ~ I ·r f.
```

While this data is not enough to capture a fully coherent idempotent map, it is
sufficient for showing that `f` can be made to be fully coherent. This is in
contrast to [idempotent maps](foundation.idempotent-maps.md), which may in
general fail to be coherent.

**Terminology.** Our definition of a _quasicoherently idempotent map_
corresponds to the definition of a _quasiidempotent map_ in {{#reference Shu17}}
and {{#reference Shu14SplittingIdempotents}}.

## Definitions

### The structure of quasicoherent idempotence on maps

```agda
coherence-is-quasicoherently-idempotent-map :
  {l : Level} {A : UU l} (f : A → A) → f ∘ f ~ f → UU l
coherence-is-quasicoherently-idempotent-map f I = f ·l I ~ I ·r f

is-quasicoherently-idempotent-map : {l : Level} {A : UU l} → (A → A) → UU l
is-quasicoherently-idempotent-map f =
  Σ (f ∘ f ~ f) (coherence-is-quasicoherently-idempotent-map f)

module _
  {l : Level} {A : UU l} {f : A → A} (H : is-quasicoherently-idempotent-map f)
  where

  is-idempotent-is-quasicoherently-idempotent-map : is-idempotent-map f
  is-idempotent-is-quasicoherently-idempotent-map = pr1 H

  coh-is-quasicoherently-idempotent-map :
    coherence-is-quasicoherently-idempotent-map f
      ( is-idempotent-is-quasicoherently-idempotent-map)
  coh-is-quasicoherently-idempotent-map = pr2 H
```

### The type of quasicoherently idempotent maps

```agda
quasicoherently-idempotent-map : {l : Level} (A : UU l) → UU l
quasicoherently-idempotent-map A = Σ (A → A) (is-quasicoherently-idempotent-map)

module _
  {l : Level} {A : UU l} (H : quasicoherently-idempotent-map A)
  where

  map-quasicoherently-idempotent-map : A → A
  map-quasicoherently-idempotent-map = pr1 H

  is-quasicoherently-idempotent-quasicoherently-idempotent-map :
    is-quasicoherently-idempotent-map map-quasicoherently-idempotent-map
  is-quasicoherently-idempotent-quasicoherently-idempotent-map = pr2 H

  is-idempotent-quasicoherently-idempotent-map :
    is-idempotent-map map-quasicoherently-idempotent-map
  is-idempotent-quasicoherently-idempotent-map =
    is-idempotent-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map)

  coh-quasicoherently-idempotent-map :
    coherence-is-quasicoherently-idempotent-map
      ( map-quasicoherently-idempotent-map)
      ( is-idempotent-quasicoherently-idempotent-map)
  coh-quasicoherently-idempotent-map =
    coh-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map)

  idempotent-map-quasicoherently-idempotent-map : idempotent-map A
  idempotent-map-quasicoherently-idempotent-map =
    ( map-quasicoherently-idempotent-map ,
      is-idempotent-quasicoherently-idempotent-map)
```

## Properties

### Being quasicoherently idempotent on a set is a property

```agda
module _
  {l : Level} {A : UU l} (is-set-A : is-set A) (f : A → A)
  where

  is-prop-coherence-is-quasicoherently-idempotent-map-is-set :
    (I : f ∘ f ~ f) → is-prop (coherence-is-quasicoherently-idempotent-map f I)
  is-prop-coherence-is-quasicoherently-idempotent-map-is-set I =
    is-prop-Π
      ( λ x →
        is-set-is-prop
          ( is-set-A ((f ∘ f ∘ f) x) ((f ∘ f) x))
          ( (f ·l I) x)
          ( (I ·r f) x))

  is-prop-is-quasicoherently-idempotent-map-is-set :
    is-prop (is-quasicoherently-idempotent-map f)
  is-prop-is-quasicoherently-idempotent-map-is-set =
    is-prop-Σ
      ( is-prop-is-idempotent-map-is-set is-set-A f)
      ( is-prop-coherence-is-quasicoherently-idempotent-map-is-set)

  is-quasicoherently-idempotent-map-is-set-Prop : Prop l
  is-quasicoherently-idempotent-map-is-set-Prop =
    ( is-quasicoherently-idempotent-map f ,
      is-prop-is-quasicoherently-idempotent-map-is-set)

module _
  {l : Level} (A : Set l) (f : type-Set A → type-Set A)
  where

  is-prop-is-quasicoherently-idempotent-map-Set :
    is-prop (is-quasicoherently-idempotent-map f)
  is-prop-is-quasicoherently-idempotent-map-Set =
    is-prop-is-quasicoherently-idempotent-map-is-set (is-set-type-Set A) f

  is-quasicoherently-idempotent-map-prop-Set : Prop l
  is-quasicoherently-idempotent-map-prop-Set =
    ( is-quasicoherently-idempotent-map f ,
      is-prop-is-quasicoherently-idempotent-map-Set)
```

### Idempotent maps on sets are quasicoherently idempotent

```agda
module _
  {l : Level} {A : UU l} (is-set-A : is-set A) {f : A → A}
  where

  is-quasicoherently-idempotent-is-idempotent-map-is-set :
    is-idempotent-map f → is-quasicoherently-idempotent-map f
  pr1 (is-quasicoherently-idempotent-is-idempotent-map-is-set I) = I
  pr2 (is-quasicoherently-idempotent-is-idempotent-map-is-set I) x =
    eq-is-prop (is-set-A ((f ∘ f ∘ f) x) ((f ∘ f) x))
```

### If `i` and `r` is an inclusion-retraction pair, then `i ∘ r` is quasicoherently idempotent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (i : B → A) (r : A → B) (H : is-retraction i r)
  where

  coherence-is-quasicoherently-idempotent-inclusion-retraction :
    coherence-is-quasicoherently-idempotent-map (i ∘ r)
      ( is-idempotent-inclusion-retraction i r H)
  coherence-is-quasicoherently-idempotent-inclusion-retraction =
    ( inv-preserves-comp-left-whisker-comp i r (i ·l H ·r r)) ∙h
    ( double-whisker-comp²
      ( i)
      ( preserves-comp-left-whisker-comp r i H ∙h inv-coh-htpy-id H)
      ( r))

  is-quasicoherently-idempotent-inclusion-retraction :
    is-quasicoherently-idempotent-map (i ∘ r)
  is-quasicoherently-idempotent-inclusion-retraction =
    ( is-idempotent-inclusion-retraction i r H ,
      coherence-is-quasicoherently-idempotent-inclusion-retraction)
```

### Quasicoherent idempotence is preserved by homotopies

```agda
module _
  {l : Level} {A : UU l} {f g : A → A} (F : is-quasicoherently-idempotent-map f)
  where

  abstract
    coherence-is-quasicoherently-idempotent-map-htpy :
      (H : g ~ f) →
      coherence-is-quasicoherently-idempotent-map g
        ( is-idempotent-map-htpy
          ( is-idempotent-is-quasicoherently-idempotent-map F)
          ( H))
    coherence-is-quasicoherently-idempotent-map-htpy H =
      ( right-transpose-htpy-concat
        ( g ·l
          is-idempotent-map-htpy
            ( is-idempotent-is-quasicoherently-idempotent-map F)
            ( H))
        ( H ·r g)
        ( H ·r (g ∘ g) ∙h
          ( ( f) ·l
            ( g ·l H ∙h
              H ·r f ∙h
              is-idempotent-is-quasicoherently-idempotent-map F ∙h inv-htpy H)))
        ( inv-htpy
          ( ( nat-htpy H) ∘
            ( g ·l H ∙h
              H ·r f ∙h
              is-idempotent-is-quasicoherently-idempotent-map F ∙h
              inv-htpy H)))) ∙h
      ( ap-concat-htpy'
        ( inv-htpy (H ·r g))
        ( ( ap-concat-htpy
            ( H ·r ((g ∘ g)))
            ( ( distributive-left-whisker-comp-concat f
                ( g ·l H ∙h
                  H ·r f ∙h
                  is-idempotent-is-quasicoherently-idempotent-map F)
                ( inv-htpy H)) ∙h
              ( ap-concat-htpy'
                ( f ·l inv-htpy H)
                ( ( distributive-left-whisker-comp-concat f
                    ( g ·l H ∙h H ·r f)
                    ( is-idempotent-is-quasicoherently-idempotent-map F)) ∙h
                  ( ap-binary-concat-htpy
                    ( distributive-left-whisker-comp-concat f
                      ( g ·l H)
                      ( H ·r f))
                    ( coh-is-quasicoherently-idempotent-map F)))) ∙h
              ( assoc-htpy
                ( f ·l g ·l H ∙h f ·l H ·r f)
                ( is-idempotent-is-quasicoherently-idempotent-map F ·r f)
                ( f ·l inv-htpy H)) ∙h
              ( ap-concat-htpy
                ( f ·l g ·l H ∙h f ·l H ·r f)
                ( ( nat-htpy
                    ( is-idempotent-is-quasicoherently-idempotent-map F)) ∘
                  ( inv-htpy H))) ∙h
              ( inv-htpy
                ( assoc-htpy
                  ( f ·l g ·l H ∙h f ·l H ·r f)
                  ( (f ∘ f) ·l inv-htpy H)
                  ( is-idempotent-is-quasicoherently-idempotent-map F ·r
                    g))))) ∙h
          ( inv-htpy
            ( assoc-htpy
              ( H ·r (g ∘ g))
              ( f ·l g ·l H ∙h f ·l H ·r f ∙h (f ∘ f) ·l inv-htpy H)
              ( is-idempotent-is-quasicoherently-idempotent-map F ·r g))) ∙h
          ( ap-concat-htpy'
            ( is-idempotent-is-quasicoherently-idempotent-map F ·r g)
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

  is-quasicoherently-idempotent-map-htpy :
    g ~ f → is-quasicoherently-idempotent-map g
  pr1 (is-quasicoherently-idempotent-map-htpy H) =
    is-idempotent-map-htpy
      ( is-idempotent-is-quasicoherently-idempotent-map F)
      ( H)
  pr2 (is-quasicoherently-idempotent-map-htpy H) =
    coherence-is-quasicoherently-idempotent-map-htpy H

  is-quasicoherently-idempotent-map-inv-htpy :
    f ~ g → is-quasicoherently-idempotent-map g
  pr1 (is-quasicoherently-idempotent-map-inv-htpy H) =
    is-idempotent-map-htpy
      ( is-idempotent-is-quasicoherently-idempotent-map F)
      ( inv-htpy H)
  pr2 (is-quasicoherently-idempotent-map-inv-htpy H) =
    coherence-is-quasicoherently-idempotent-map-htpy (inv-htpy H)
```

### Realigning the coherence of quasicoherent idempotence

Given a quasicoherently idempotent `f` then any other idempotence homotopy
`H : f ∘ f ~ f` that is homotopic to the coherent one is also coherent.

```agda
module _
  {l : Level} {A : UU l} {f : A → A}
  (F : is-quasicoherently-idempotent-map f)
  (I : f ∘ f ~ f)
  where

  coherence-is-quasicoherently-idempotent-is-idempotent-map-htpy :
    is-idempotent-is-quasicoherently-idempotent-map F ~ I →
    coherence-is-quasicoherently-idempotent-map f I
  coherence-is-quasicoherently-idempotent-is-idempotent-map-htpy α =
    ( left-whisker-comp² f (inv-htpy α)) ∙h
    ( coh-is-quasicoherently-idempotent-map F) ∙h
    ( right-whisker-comp² α f)

  coherence-is-quasicoherently-idempotent-is-idempotent-map-inv-htpy :
    I ~ is-idempotent-is-quasicoherently-idempotent-map F →
    coherence-is-quasicoherently-idempotent-map f I
  coherence-is-quasicoherently-idempotent-is-idempotent-map-inv-htpy α =
    ( left-whisker-comp² f α) ∙h
    ( coh-is-quasicoherently-idempotent-map F) ∙h
    ( right-whisker-comp² (inv-htpy α) f)

  is-quasicoherently-idempotent-is-idempotent-map-htpy :
    is-idempotent-is-quasicoherently-idempotent-map F ~ I →
    is-quasicoherently-idempotent-map f
  is-quasicoherently-idempotent-is-idempotent-map-htpy α =
    ( I , coherence-is-quasicoherently-idempotent-is-idempotent-map-htpy α)

  is-quasicoherently-idempotent-is-idempotent-map-inv-htpy :
    I ~ is-idempotent-is-quasicoherently-idempotent-map F →
    is-quasicoherently-idempotent-map f
  is-quasicoherently-idempotent-is-idempotent-map-inv-htpy α =
    ( I ,
      coherence-is-quasicoherently-idempotent-is-idempotent-map-inv-htpy α)
```

### Not every idempotent map is quasicoherently idempotent

A counterexample can be constructed using the
[cantor space](set-theory.cantor-space.md). See Section 4 of {{#cite Shu17}} for
more details. Note that the statement does not ask for the idempotence witness
`I : f ∘ f ~ f` to be preserved.

## See also

- In [`foundation.split-idempotent-maps`](foundation.split-idempotent-maps.md)
  we show that every quasicoherently idempotent splits. In fact, split
  idempotents are a retract of quasicoherently idempotents.

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
