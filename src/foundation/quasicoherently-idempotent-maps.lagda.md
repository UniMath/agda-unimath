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
{{#concept "quasicoherently idempotent map" Disambiguation="on a type" Agda=is-quasicoherently-idempotent}}
is a map `f : A → A` [equipped](foundation.structure.md) with a
[homotopy](foundation-core.homotopies.md) `I : f ∘ f ~ f` witnessing that `f` is
[idempotent](foundation.idempotent-maps.md), and a coherence

```text
  f ·l I ~ I ·r f.
```

While this data is not enough to capture a fully coherent idempotent map, it is
sufficient for showing that `f` can be made to be fully coherent. This is in
contrast to [idempotent maps](foundation.idempotent-maps.md), which may in
general fail to be coherent.

**Terminology.** Our definition of a _quasicoherently idempotent map_
corresponds to the definition of a _quasiidempotent map_ in {{#cite Shu17}} and
{{#cite Shu14SplittingIdempotents}}.

## Definitions

### The structure of quasicoherent idempotence on maps

```agda
coherence-is-quasicoherently-idempotent :
  {l : Level} {A : UU l} (f : A → A) → f ∘ f ~ f → UU l
coherence-is-quasicoherently-idempotent f I = f ·l I ~ I ·r f

is-quasicoherently-idempotent : {l : Level} {A : UU l} → (A → A) → UU l
is-quasicoherently-idempotent f =
  Σ (f ∘ f ~ f) (coherence-is-quasicoherently-idempotent f)

module _
  {l : Level} {A : UU l} {f : A → A} (H : is-quasicoherently-idempotent f)
  where

  is-idempotent-is-quasicoherently-idempotent : is-idempotent f
  is-idempotent-is-quasicoherently-idempotent = pr1 H

  coh-is-quasicoherently-idempotent :
    coherence-is-quasicoherently-idempotent f
      ( is-idempotent-is-quasicoherently-idempotent)
  coh-is-quasicoherently-idempotent = pr2 H
```

### The type of quasicoherently idempotent maps

```agda
quasicoherently-idempotent-map : {l : Level} (A : UU l) → UU l
quasicoherently-idempotent-map A = Σ (A → A) (is-quasicoherently-idempotent)

module _
  {l : Level} {A : UU l} (H : quasicoherently-idempotent-map A)
  where

  map-quasicoherently-idempotent-map : A → A
  map-quasicoherently-idempotent-map = pr1 H

  is-quasicoherently-idempotent-quasicoherently-idempotent-map :
    is-quasicoherently-idempotent map-quasicoherently-idempotent-map
  is-quasicoherently-idempotent-quasicoherently-idempotent-map = pr2 H

  is-idempotent-quasicoherently-idempotent-map :
    is-idempotent map-quasicoherently-idempotent-map
  is-idempotent-quasicoherently-idempotent-map =
    is-idempotent-is-quasicoherently-idempotent
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map)

  coh-quasicoherently-idempotent-map :
    coherence-is-quasicoherently-idempotent
      ( map-quasicoherently-idempotent-map)
      ( is-idempotent-quasicoherently-idempotent-map)
  coh-quasicoherently-idempotent-map =
    coh-is-quasicoherently-idempotent
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

  is-prop-coherence-is-quasicoherently-idempotent-is-set :
    (I : f ∘ f ~ f) → is-prop (coherence-is-quasicoherently-idempotent f I)
  is-prop-coherence-is-quasicoherently-idempotent-is-set I =
    is-prop-Π
      ( λ x →
        is-set-is-prop
          ( is-set-A ((f ∘ f ∘ f) x) ((f ∘ f) x))
          ( (f ·l I) x)
          ( (I ·r f) x))

  is-prop-is-quasicoherently-idempotent-is-set :
    is-prop (is-quasicoherently-idempotent f)
  is-prop-is-quasicoherently-idempotent-is-set =
    is-prop-Σ
      ( is-prop-is-idempotent-is-set is-set-A f)
      ( is-prop-coherence-is-quasicoherently-idempotent-is-set)

  is-quasicoherently-idempotent-is-set-Prop : Prop l
  is-quasicoherently-idempotent-is-set-Prop =
    ( is-quasicoherently-idempotent f ,
      is-prop-is-quasicoherently-idempotent-is-set)

module _
  {l : Level} (A : Set l) (f : type-Set A → type-Set A)
  where

  is-prop-is-quasicoherently-idempotent-Set :
    is-prop (is-quasicoherently-idempotent f)
  is-prop-is-quasicoherently-idempotent-Set =
    is-prop-is-quasicoherently-idempotent-is-set (is-set-type-Set A) f

  is-quasicoherently-idempotent-prop-Set : Prop l
  is-quasicoherently-idempotent-prop-Set =
    ( is-quasicoherently-idempotent f ,
      is-prop-is-quasicoherently-idempotent-Set)
```

### Idempotent maps on sets are quasicoherently idempotent

```agda
module _
  {l : Level} {A : UU l} (is-set-A : is-set A) {f : A → A}
  where

  is-quasicoherently-idempotent-is-idempotent-is-set :
    is-idempotent f → is-quasicoherently-idempotent f
  pr1 (is-quasicoherently-idempotent-is-idempotent-is-set I) = I
  pr2 (is-quasicoherently-idempotent-is-idempotent-is-set I) x =
    eq-is-prop (is-set-A ((f ∘ f ∘ f) x) ((f ∘ f) x))
```

### If `i` and `r` form an inclusion-retraction pair, then `i ∘ r` is quasicoherently idempotent

This statement can be found as part of the proof of Lemma 3.6 in
{{#cite Shu17}}.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (i : B → A) (r : A → B) (H : is-retraction i r)
  where

  coherence-is-quasicoherently-idempotent-inclusion-retraction :
    coherence-is-quasicoherently-idempotent
      ( i ∘ r)
      ( is-idempotent-inclusion-retraction i r H)
  coherence-is-quasicoherently-idempotent-inclusion-retraction =
    ( inv-preserves-comp-left-whisker-comp i r (i ·l H ·r r)) ∙h
    ( double-whisker-comp²
      ( i)
      ( preserves-comp-left-whisker-comp r i H ∙h inv-coh-htpy-id H)
      ( r))

  is-quasicoherently-idempotent-inclusion-retraction :
    is-quasicoherently-idempotent (i ∘ r)
  is-quasicoherently-idempotent-inclusion-retraction =
    ( is-idempotent-inclusion-retraction i r H ,
      coherence-is-quasicoherently-idempotent-inclusion-retraction)
```

### Quasicoherent idempotence is preserved by homotopies

```agda
module _
  {l : Level} {A : UU l} {f g : A → A} (F : is-quasicoherently-idempotent f)
  where

  abstract
    coherence-is-quasicoherently-idempotent-htpy :
      (H : g ~ f) →
      coherence-is-quasicoherently-idempotent g
        ( is-idempotent-htpy
          ( is-idempotent-is-quasicoherently-idempotent F)
          ( H))
    coherence-is-quasicoherently-idempotent-htpy H =
      homotopy-reasoning
      ( g ·l is-idempotent-htpy I H)
      ~ ( H ·r (g ∘ g)) ∙h
        ( f ·l (g ·l H ∙h H ·r f ∙h I ∙h inv-htpy H)) ∙h
        ( inv-htpy (H ·r g))
      by
      ( right-transpose-htpy-concat
        ( g ·l is-idempotent-htpy I H)
        ( H ·r g)
        ( H ·r (g ∘ g) ∙h (f ·l (g ·l H ∙h H ·r f ∙h I ∙h inv-htpy H)))
        ( inv-htpy (nat-htpy H ∘ (g ·l H ∙h H ·r f ∙h I ∙h inv-htpy H))))
      ~ g ·l H ·r g ∙h H ·r (f ∘ g) ∙h I ·r g ∙h inv-htpy (H ·r g)
      by
      ( ap-concat-htpy'
        ( inv-htpy (H ·r g))
        ( ( ap-concat-htpy
            ( H ·r ((g ∘ g)))
            ( ( distributive-left-whisker-comp-concat f
                ( g ·l H ∙h H ·r f ∙h I)
                ( inv-htpy H)) ∙h
              ( ap-concat-htpy'
                ( f ·l inv-htpy H)
                ( ( distributive-left-whisker-comp-concat f
                    ( g ·l H ∙h H ·r f)
                    ( I)) ∙h
                  ( ap-binary-concat-htpy
                    ( distributive-left-whisker-comp-concat f (g ·l H) (H ·r f))
                    ( coh-is-quasicoherently-idempotent F)))) ∙h
              ( assoc-htpy
                ( f ·l g ·l H ∙h f ·l H ·r f)
                ( I ·r f)
                ( f ·l inv-htpy H)) ∙h
              ( ap-concat-htpy
                ( f ·l g ·l H ∙h f ·l H ·r f)
                ( nat-htpy I ∘ inv-htpy H)) ∙h
              ( inv-htpy
                ( assoc-htpy
                  ( f ·l g ·l H ∙h f ·l H ·r f)
                  ( (f ∘ f) ·l inv-htpy H)
                  ( I ·r g))))) ∙h
          ( inv-htpy
            ( assoc-htpy
              ( H ·r (g ∘ g))
              ( f ·l g ·l H ∙h f ·l H ·r f ∙h (f ∘ f) ·l inv-htpy H)
              ( I ·r g))) ∙h
          ( ap-concat-htpy'
            ( I ·r g)
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
                  ( is-retraction-inv-concat-htpy'
                    ( (f ∘ f) ·l H)
                    ( f ·l H ·r g)))) ∙h
              ( nat-htpy H ∘ (H ·r g))))))
      where
        I : is-idempotent f
        I = is-idempotent-is-quasicoherently-idempotent F

  is-quasicoherently-idempotent-htpy :
    g ~ f → is-quasicoherently-idempotent g
  pr1 (is-quasicoherently-idempotent-htpy H) =
    is-idempotent-htpy
      ( is-idempotent-is-quasicoherently-idempotent F)
      ( H)
  pr2 (is-quasicoherently-idempotent-htpy H) =
    coherence-is-quasicoherently-idempotent-htpy H

  is-quasicoherently-idempotent-inv-htpy :
    f ~ g → is-quasicoherently-idempotent g
  pr1 (is-quasicoherently-idempotent-inv-htpy H) =
    is-idempotent-htpy
      ( is-idempotent-is-quasicoherently-idempotent F)
      ( inv-htpy H)
  pr2 (is-quasicoherently-idempotent-inv-htpy H) =
    coherence-is-quasicoherently-idempotent-htpy (inv-htpy H)
```

### Realigning the coherence of a quasicoherent idempotence proof

Given a quasicoherently idempotent map `f`, any other idempotence homotopy
`I : f ∘ f ~ f` that is homotopic to the coherent one is also coherent.

```agda
module _
  {l : Level} {A : UU l} {f : A → A}
  (F : is-quasicoherently-idempotent f)
  (I : f ∘ f ~ f)
  where

  coherence-is-quasicoherently-idempotent-is-idempotent-htpy :
    is-idempotent-is-quasicoherently-idempotent F ~ I →
    coherence-is-quasicoherently-idempotent f I
  coherence-is-quasicoherently-idempotent-is-idempotent-htpy α =
    ( left-whisker-comp² f (inv-htpy α)) ∙h
    ( coh-is-quasicoherently-idempotent F) ∙h
    ( right-whisker-comp² α f)

  coherence-is-quasicoherently-idempotent-is-idempotent-inv-htpy :
    I ~ is-idempotent-is-quasicoherently-idempotent F →
    coherence-is-quasicoherently-idempotent f I
  coherence-is-quasicoherently-idempotent-is-idempotent-inv-htpy α =
    ( left-whisker-comp² f α) ∙h
    ( coh-is-quasicoherently-idempotent F) ∙h
    ( right-whisker-comp² (inv-htpy α) f)

  is-quasicoherently-idempotent-is-idempotent-htpy :
    is-idempotent-is-quasicoherently-idempotent F ~ I →
    is-quasicoherently-idempotent f
  is-quasicoherently-idempotent-is-idempotent-htpy α =
    ( I , coherence-is-quasicoherently-idempotent-is-idempotent-htpy α)

  is-quasicoherently-idempotent-is-idempotent-inv-htpy :
    I ~ is-idempotent-is-quasicoherently-idempotent F →
    is-quasicoherently-idempotent f
  is-quasicoherently-idempotent-is-idempotent-inv-htpy α =
    ( I , coherence-is-quasicoherently-idempotent-is-idempotent-inv-htpy α)
```

### Not every idempotent map is quasicoherently idempotent

A counterexample can be constructed using the
[cantor space](set-theory.cantor-space.md). See Section 4 of {{#cite Shu17}} for
more details. Note that the statement does not ask for the idempotence witness
`I : f ∘ f ~ f` to be preserved.

## See also

- In [`foundation.split-idempotent-maps`](foundation.split-idempotent-maps.md)
  we show that every quasicoherently idempotent map splits. Moreover, it is true
  that split idempotent maps are a retract of quasicoherent idempotent maps.

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
