# Coforks

```agda
module synthetic-homotopy-theory.coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.codiagonal-maps-of-types
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

A **cofork** of a parallel pair `f, g : A → B` with vertext `X` is a map
`e : B → X` together with a [homotopy](foundation.homotopies.md)
`H : e ∘ f ~ e ∘ g`. The name comes from the diagram

```text
     g
   ----->     e
 A -----> B -----> X
     f
```

which looks like a fork if you flip the arrows, hence a cofork.

Coforks are an analogue of
[cocones under spans](synthetic-homotopy-theory.cocones-under-spans.md) for
parallel pairs. The universal cofork of a pair is their
[coequalizer](synthetic-homotopy-theory.coequalizers.md).

## Definitions

### Coforks

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  cofork : UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  cofork X = Σ (B → X) (λ e → e ∘ f ~ e ∘ g)

  module _
    { X : UU l3} (e : cofork X)
    where

    map-cofork : B → X
    map-cofork = pr1 e

    coherence-cofork : map-cofork ∘ f ~ map-cofork ∘ g
    coherence-cofork = pr2 e
```

### Homotopies of coforks

A homotopy between coforks with the same vertex is given by a homotopy between
the two maps, together with a coherence datum asserting that we may apply the
given homotopy and the appropriate cofork homotopy in either order.

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  where

  coherence-htpy-cofork :
    ( e e' : cofork f g X) →
    ( K : map-cofork f g e ~ map-cofork f g e') →
    UU (l1 ⊔ l3)
  coherence-htpy-cofork e e' K =
    ( (coherence-cofork f g e) ∙h (K ·r g)) ~
    ( (K ·r f) ∙h (coherence-cofork f g e'))

  htpy-cofork : cofork f g X → cofork f g X → UU (l1 ⊔ l2 ⊔ l3)
  htpy-cofork e e' =
    Σ ( map-cofork f g e ~ map-cofork f g e')
      ( coherence-htpy-cofork e e')
```

### Postcomposing coforks

Given a cofork `e : B → X` and a map `h : X → Y`, we may compose the two to get
a new cofork `h ∘ e`.

```text
     g
   ----->     e        h
 A -----> B -----> X -----> Y
     f
```

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  { X : UU l3} (e : cofork f g X)
  where

  cofork-map : {l : Level} {Y : UU l} → (X → Y) → cofork f g Y
  pr1 (cofork-map h) = h ∘ map-cofork f g e
  pr2 (cofork-map h) = h ·l (coherence-cofork f g e)
```

## Properties

### Characterization of identity types of coforks

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  where

  reflexive-htpy-cofork : (e : cofork f g X) → htpy-cofork f g e e
  pr1 (reflexive-htpy-cofork e) = refl-htpy
  pr2 (reflexive-htpy-cofork e) = right-unit-htpy

  htpy-cofork-eq :
    ( e e' : cofork f g X) → (e ＝ e') → htpy-cofork f g e e'
  htpy-cofork-eq e .e refl = reflexive-htpy-cofork e

  abstract
    is-contr-total-htpy-cofork :
      ( e : cofork f g X) → is-contr (Σ (cofork f g X) (htpy-cofork f g e))
    is-contr-total-htpy-cofork e =
      is-contr-total-Eq-structure
        ( ev-pair (coherence-htpy-cofork f g e))
        ( is-contr-total-htpy (map-cofork f g e))
        ( map-cofork f g e , refl-htpy)
        ( is-contr-is-equiv'
          ( Σ ( map-cofork f g e ∘ f ~ map-cofork f g e ∘ g)
              ( λ K → coherence-cofork f g e ~ K))
          ( tot (λ K M → right-unit-htpy ∙h M))
          ( is-equiv-tot-is-fiberwise-equiv
            ( is-equiv-concat-htpy right-unit-htpy))
          ( is-contr-total-htpy (coherence-cofork f g e)))

    is-equiv-htpy-cofork-eq :
      ( e e' : cofork f g X) → is-equiv (htpy-cofork-eq e e')
    is-equiv-htpy-cofork-eq e =
      fundamental-theorem-id (is-contr-total-htpy-cofork e) (htpy-cofork-eq e)

  eq-htpy-cofork :
    ( e e' : cofork f g X) → htpy-cofork f g e e' → e ＝ e'
  eq-htpy-cofork e e' = map-inv-is-equiv (is-equiv-htpy-cofork-eq e e')
```

### Postcomposing a cofork by identity is the identity

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X)
  where

  cofork-map-id : cofork-map f g e id ＝ e
  cofork-map-id =
    eq-htpy-cofork f g
      ( cofork-map f g e id)
      ( e)
      (refl-htpy , (right-unit-htpy ∙h (ap-id ∘ coherence-cofork f g e)))
```

### Postcomposing coforks distributes over function composition

```text
     g
   ----->     e        h        k
 A -----> B -----> X -----> Y -----> Z
     f
```

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  { X : UU l3} {Y : UU l4} {Z : UU l5}
  ( e : cofork f g X)
  where

  cofork-map-comp :
    (h : X → Y) (k : Y → Z) →
    cofork-map f g e (k ∘ h) ＝ cofork-map f g (cofork-map f g e h) k
  cofork-map-comp h k =
    eq-htpy-cofork f g
      ( cofork-map f g e (k ∘ h))
      ( cofork-map f g (cofork-map f g e h) k)
      ( refl-htpy , (right-unit-htpy ∙h (ap-comp k h ∘ coherence-cofork f g e)))
```

### Coforks are special cases of cocones under spans

The type of coforks of parallel pairs is equivalent to the type of
[cocones](synthetic-homotopy-theory.cocones-under-spans.md) under the span

```text
     ∇         [f,g]
A <----- A + A -----> B.
```

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  module _
    { l3 : Level} {X : UU l3}
    where

    cofork-cocone-codiagonal :
      cocone (codiagonal A) (ind-coprod (λ _ → B) f g) X →
      cofork f g X
    pr1 (cofork-cocone-codiagonal c) =
      vertical-map-cocone (codiagonal A) (ind-coprod (λ _ → B) f g) c
    pr2 (cofork-cocone-codiagonal c) =
      ( ( inv-htpy
          ( coherence-square-cocone
            ( codiagonal A)
            ( ind-coprod (λ _ → B) f g)
            ( c))) ·r
        ( inl)) ∙h
      ( ( coherence-square-cocone
          ( codiagonal A)
          ( ind-coprod (λ _ → B) f g)
          ( c)) ·r
        ( inr))

    cocone-codiagonal-cofork :
      cofork f g X →
      cocone (codiagonal A) (ind-coprod (λ _ → B) f g) X
    pr1 (cocone-codiagonal-cofork e) = map-cofork f g e ∘ f
    pr1 (pr2 (cocone-codiagonal-cofork e)) = map-cofork f g e
    pr2 (pr2 (cocone-codiagonal-cofork e)) (inl a) = refl
    pr2 (pr2 (cocone-codiagonal-cofork e)) (inr a) = coherence-cofork f g e a

    abstract
      is-section-cocone-codiagonal-cofork :
        cofork-cocone-codiagonal ∘ cocone-codiagonal-cofork ~ id
      is-section-cocone-codiagonal-cofork e =
        eq-htpy-cofork f g
          ( cofork-cocone-codiagonal (cocone-codiagonal-cofork e))
          ( e)
          ( refl-htpy , right-unit-htpy)

      is-retraction-cocone-codiagonal-fork :
        cocone-codiagonal-cofork ∘ cofork-cocone-codiagonal ~ id
      is-retraction-cocone-codiagonal-fork c =
        eq-htpy-cocone
          ( codiagonal A)
          ( ind-coprod (λ _ → B) f g)
          ( cocone-codiagonal-cofork (cofork-cocone-codiagonal c))
          ( c)
          ( ( ( inv-htpy
                ( coherence-square-cocone
                  ( codiagonal A)
                  ( ind-coprod (λ _ → B) f g)
                  ( c))) ·r
              ( inl)) ,
            ( refl-htpy) ,
            ( λ where
              (inl a) →
                inv
                  ( left-inv
                    ( coherence-square-cocone
                      ( codiagonal A)
                      ( ind-coprod (λ _ → B) f g)
                      ( c)
                      ( inl a)))
              (inr a) → right-unit))

    is-equiv-cofork-cocone-codiagonal :
      is-equiv cofork-cocone-codiagonal
    is-equiv-cofork-cocone-codiagonal =
      is-equiv-is-invertible
        ( cocone-codiagonal-cofork)
        ( is-section-cocone-codiagonal-cofork)
        ( is-retraction-cocone-codiagonal-fork)

    equiv-cocone-codiagonal-cofork :
      cocone (codiagonal A) (ind-coprod (λ _ → B) f g) X ≃
      cofork f g X
    pr1 equiv-cocone-codiagonal-cofork = cofork-cocone-codiagonal
    pr2 equiv-cocone-codiagonal-cofork = is-equiv-cofork-cocone-codiagonal

  triangle-cofork-cocone :
    { l3 l4 : Level} {X : UU l3} {Y : UU l4} →
    ( c : cocone (codiagonal A) (ind-coprod (λ _ → B) f g) X) →
    coherence-triangle-maps
      ( cofork-map f g (cofork-cocone-codiagonal c) {Y = Y})
      ( cofork-cocone-codiagonal)
      ( cocone-map (codiagonal A) (ind-coprod (λ _ → B) f g) c)
  triangle-cofork-cocone c h =
    eq-htpy-cofork f g
      ( cofork-map f g (cofork-cocone-codiagonal c) h)
      ( cofork-cocone-codiagonal
        ( cocone-map (codiagonal A) (ind-coprod (λ _ → B) f g) c h))
      ( refl-htpy ,
        ( right-unit-htpy ∙h
          ( λ a →
            ( ap-concat h
              ( inv
                ( coherence-square-cocone
                  ( codiagonal A)
                  ( ind-coprod (λ _ → B) f g)
                  ( c)
                  ( inl a)))
              ( coherence-square-cocone
                ( codiagonal A)
                ( ind-coprod (λ _ → B) f g)
                ( c)
                ( inr a))) ∙
            ( identification-right-whisk
              ( ap-inv h
                ( coherence-square-cocone
                  ( codiagonal A)
                  ( ind-coprod (λ _ → B) f g)
                  ( c)
                  ( inl a)))
              ( ap h
                ( coherence-square-cocone
                  ( codiagonal A)
                  ( ind-coprod (λ _ → B) f g)
                  ( c)
                  ( inr a)))))))
```
