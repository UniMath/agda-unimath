# Quasicoherently idempotent maps

```agda
module foundation.quasicoherently-idempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-algebra
open import foundation.homotopy-induction
open import foundation.idempotent-maps
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sets

open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.loop-homotopy-circle
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
quasicoherence-is-idempotent :
  {l : Level} {A : UU l} (f : A → A) → f ∘ f ~ f → UU l
quasicoherence-is-idempotent f I = f ·l I ~ I ·r f

is-quasicoherently-idempotent : {l : Level} {A : UU l} → (A → A) → UU l
is-quasicoherently-idempotent f =
  Σ (f ∘ f ~ f) (quasicoherence-is-idempotent f)

module _
  {l : Level} {A : UU l} {f : A → A} (H : is-quasicoherently-idempotent f)
  where

  is-idempotent-is-quasicoherently-idempotent : is-idempotent f
  is-idempotent-is-quasicoherently-idempotent = pr1 H

  coh-is-quasicoherently-idempotent :
    quasicoherence-is-idempotent f
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
    quasicoherence-is-idempotent
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

### The identity function is quasicoherently idempotent

In fact, any idempotence witness of the identity function is quasicoherent.

```agda
module _
  {l : Level} {A : UU l} (H : is-idempotent (id {A = A}))
  where

  quasicoherence-is-idempotent-id :
    quasicoherence-is-idempotent id H
  quasicoherence-is-idempotent-id = left-unit-law-left-whisker-comp H

  is-quasicoherently-idempotent-is-idempotent-id :
    is-quasicoherently-idempotent (id {A = A})
  is-quasicoherently-idempotent-is-idempotent-id =
    ( H , quasicoherence-is-idempotent-id)

module _
  {l : Level} {A : UU l}
  where

  is-quasicoherently-idempotent-id :
    is-quasicoherently-idempotent (id {A = A})
  is-quasicoherently-idempotent-id =
    is-quasicoherently-idempotent-is-idempotent-id refl-htpy
```

### Being quasicoherently idempotent on a set is a property

```agda
module _
  {l : Level} {A : UU l} (is-set-A : is-set A) (f : A → A)
  where

  is-prop-quasicoherence-is-idempotent-is-set :
    (I : f ∘ f ~ f) → is-prop (quasicoherence-is-idempotent f I)
  is-prop-quasicoherence-is-idempotent-is-set I =
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
      ( is-prop-quasicoherence-is-idempotent-is-set)

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

### Being quasicoherently idempotent is generally not a property

Not even for [1-types](foundation.1-types.md): consider the identity function on
the [circle](synthetic-homotopy-theory.circle.md)

```text
  id : 𝕊¹ → 𝕊¹.
```

Two distinct witnesses that it is idempotent are given by `t ↦ refl` and
`t ↦ loop`. Both of these are quasicoherent, because

```text
  quasicoherence-is-idempotent id I ≐ (id ·l I ~ I ·r id) ≃ (I ~ I).
```

```agda
is-not-prop-is-quasicoherently-idempotent-id-𝕊¹ :
  ¬ (is-prop (is-quasicoherently-idempotent (id {A = 𝕊¹})))
is-not-prop-is-quasicoherently-idempotent-id-𝕊¹ H =
  nonequal-Π
    ( loop-htpy-𝕊¹)
    ( refl-htpy)
    ( base-𝕊¹)
    ( is-not-refl-ev-base-loop-htpy-𝕊¹)
    ( ap pr1
      ( eq-is-prop H
        { is-quasicoherently-idempotent-is-idempotent-id loop-htpy-𝕊¹}
        { is-quasicoherently-idempotent-is-idempotent-id refl-htpy}))
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

  quasicoherence-is-idempotent-inclusion-retraction :
    quasicoherence-is-idempotent
      ( i ∘ r)
      ( is-idempotent-inclusion-retraction i r H)
  quasicoherence-is-idempotent-inclusion-retraction =
    ( inv-preserves-comp-left-whisker-comp i r (i ·l H ·r r)) ∙h
    ( double-whisker-comp²
      ( i)
      ( preserves-comp-left-whisker-comp r i H ∙h inv-coh-htpy-id H)
      ( r))

  is-quasicoherently-idempotent-inclusion-retraction :
    is-quasicoherently-idempotent (i ∘ r)
  is-quasicoherently-idempotent-inclusion-retraction =
    ( is-idempotent-inclusion-retraction i r H ,
      quasicoherence-is-idempotent-inclusion-retraction)
```

### Quasicoherent idempotence is preserved by homotopies

This fact does not explicitly appear in {{#cite Shu17}} although it is
implicitly used in Lemma 3.6.

```agda
module _
  {l : Level} {A : UU l} {f g : A → A} (F : is-quasicoherently-idempotent f)
  where

  abstract
    quasicoherence-is-idempotent-htpy :
      (H : g ~ f) →
      quasicoherence-is-idempotent g
        ( is-idempotent-htpy
          ( is-idempotent-is-quasicoherently-idempotent F)
          ( H))
    quasicoherence-is-idempotent-htpy H =
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
    quasicoherence-is-idempotent-htpy H

  is-quasicoherently-idempotent-inv-htpy :
    f ~ g → is-quasicoherently-idempotent g
  pr1 (is-quasicoherently-idempotent-inv-htpy H) =
    is-idempotent-htpy
      ( is-idempotent-is-quasicoherently-idempotent F)
      ( inv-htpy H)
  pr2 (is-quasicoherently-idempotent-inv-htpy H) =
    quasicoherence-is-idempotent-htpy (inv-htpy H)
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

  quasicoherence-is-idempotent-is-idempotent-htpy :
    is-idempotent-is-quasicoherently-idempotent F ~ I →
    quasicoherence-is-idempotent f I
  quasicoherence-is-idempotent-is-idempotent-htpy α =
    ( left-whisker-comp² f (inv-htpy α)) ∙h
    ( coh-is-quasicoherently-idempotent F) ∙h
    ( right-whisker-comp² α f)

  quasicoherence-is-idempotent-is-idempotent-inv-htpy :
    I ~ is-idempotent-is-quasicoherently-idempotent F →
    quasicoherence-is-idempotent f I
  quasicoherence-is-idempotent-is-idempotent-inv-htpy α =
    ( left-whisker-comp² f α) ∙h
    ( coh-is-quasicoherently-idempotent F) ∙h
    ( right-whisker-comp² (inv-htpy α) f)

  is-quasicoherently-idempotent-is-idempotent-htpy :
    is-idempotent-is-quasicoherently-idempotent F ~ I →
    is-quasicoherently-idempotent f
  is-quasicoherently-idempotent-is-idempotent-htpy α =
    ( I , quasicoherence-is-idempotent-is-idempotent-htpy α)

  is-quasicoherently-idempotent-is-idempotent-inv-htpy :
    I ~ is-idempotent-is-quasicoherently-idempotent F →
    is-quasicoherently-idempotent f
  is-quasicoherently-idempotent-is-idempotent-inv-htpy α =
    ( I , quasicoherence-is-idempotent-is-idempotent-inv-htpy α)
```

### Not every idempotent map is quasicoherently idempotent

To be clear, what we are asking for is an idempotent map `f`, such that _no_
idempotence homotopy `f ∘ f ~ f` is quasicoherent. A counterexample can be
constructed using the [cantor space](set-theory.cantor-space.md), see Section 4
of {{#cite Shu17}} for more details.

### Characterization of identity of quasicoherently idempotent maps

A homotopy of quasicoherent idempotence witnesses `(I, Q) ~ (J, R)` consists of
a homotopy of the underlying idempotence witnesses `H : I ~ J` and a
[coherence](foundation-core.commuting-squares-of-homotopies.md)

```text
            fH
  f ·l I -------- f ·l J
     |              |
   Q |              | R
     |              |
  I ·r f -------– J ·r f.
            Hf
```

```agda
module _
  {l : Level} {A : UU l} {f : A → A}
  where

  coherence-htpy-is-quasicoherently-idempotent :
    (p q : is-quasicoherently-idempotent f) →
    ( is-idempotent-is-quasicoherently-idempotent p ~
      is-idempotent-is-quasicoherently-idempotent q) →
    UU l
  coherence-htpy-is-quasicoherently-idempotent (I , Q) (J , R) H =
    coherence-square-homotopies
      ( left-whisker-comp² f H)
      ( Q)
      ( R)
      ( right-whisker-comp² H f)

  htpy-is-quasicoherently-idempotent :
    (p q : is-quasicoherently-idempotent f) → UU l
  htpy-is-quasicoherently-idempotent p q =
    Σ ( is-idempotent-is-quasicoherently-idempotent p ~
        is-idempotent-is-quasicoherently-idempotent q)
      ( coherence-htpy-is-quasicoherently-idempotent p q)

  refl-htpy-is-quasicoherently-idempotent :
    (p : is-quasicoherently-idempotent f) →
    htpy-is-quasicoherently-idempotent p p
  refl-htpy-is-quasicoherently-idempotent p = (refl-htpy , right-unit-htpy)

  htpy-eq-is-quasicoherently-idempotent :
    (p q : is-quasicoherently-idempotent f) →
    p ＝ q → htpy-is-quasicoherently-idempotent p q
  htpy-eq-is-quasicoherently-idempotent p .p refl =
    refl-htpy-is-quasicoherently-idempotent p

  is-torsorial-htpy-is-quasicoherently-idempotent :
    (p : is-quasicoherently-idempotent f) →
    is-torsorial (htpy-is-quasicoherently-idempotent p)
  is-torsorial-htpy-is-quasicoherently-idempotent p =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (is-idempotent-is-quasicoherently-idempotent p))
      ( is-idempotent-is-quasicoherently-idempotent p , refl-htpy)
      ( is-torsorial-htpy (coh-is-quasicoherently-idempotent p ∙h refl-htpy))

  is-equiv-htpy-eq-is-quasicoherently-idempotent :
    (p q : is-quasicoherently-idempotent f) →
    is-equiv (htpy-eq-is-quasicoherently-idempotent p q)
  is-equiv-htpy-eq-is-quasicoherently-idempotent p =
    fundamental-theorem-id
      ( is-torsorial-htpy-is-quasicoherently-idempotent p)
      ( htpy-eq-is-quasicoherently-idempotent p)

  extensionality-is-quasicoherently-idempotent :
    (p q : is-quasicoherently-idempotent f) →
    (p ＝ q) ≃ (htpy-is-quasicoherently-idempotent p q)
  extensionality-is-quasicoherently-idempotent p q =
    ( htpy-eq-is-quasicoherently-idempotent p q ,
      is-equiv-htpy-eq-is-quasicoherently-idempotent p q)

  eq-htpy-is-quasicoherently-idempotent :
    (p q : is-quasicoherently-idempotent f) →
    htpy-is-quasicoherently-idempotent p q → p ＝ q
  eq-htpy-is-quasicoherently-idempotent p q =
    map-inv-is-equiv (is-equiv-htpy-eq-is-quasicoherently-idempotent p q)
```

## See also

- In [`foundation.split-idempotent-maps`](foundation.split-idempotent-maps.md)
  we show that every quasicoherently idempotent map splits. Moreover, it is true
  that split idempotent maps are a retract of quasicoherent idempotent maps.

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
