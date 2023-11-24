# Dependent coforks

```agda
module synthetic-homotopy-theory.dependent-coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.constant-type-families
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-cocones-under-spans
```

</details>

## Idea

Given a parallel pair `f, g : A → B`, a
[cofork](synthetic-homotopy-theory.coforks.md) `e : B → X` with vertex `X`, and
a type family `P : X → 𝓤` over `X`, we may construct _dependent_ coforks on `P`
over `e`.

A **dependent cofork** on `P` over `e` consists of a dependent map

```text
k : (b : B) → P (e b)
```

and a family of
[dependent identifications](foundation.dependent-identifications.md) indexed by
`A`

```text
(a : A) → dependent-identification P (H a) (k (f a)) (k (g a)).
```

Dependent coforks are an analogue of
[dependent cocones under spans](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
for parallel pairs.

## Definitions

### Dependent coforks

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) (P : X → UU l4)
  where

  dependent-cofork : UU (l1 ⊔ l2 ⊔ l4)
  dependent-cofork =
    Σ ( (b : B) → P (map-cofork f g e b))
      ( λ k →
        ( a : A) →
        dependent-identification P
          ( coherence-cofork f g e a)
          ( k (f a))
          ( k (g a)))

module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  { e : cofork f g X} (P : X → UU l4)
  ( k : dependent-cofork f g e P)
  where

  map-dependent-cofork : (b : B) → P (map-cofork f g e b)
  map-dependent-cofork = pr1 k

  coherence-dependent-cofork :
    ( a : A) →
    dependent-identification P
      ( coherence-cofork f g e a)
      ( map-dependent-cofork (f a))
      ( map-dependent-cofork (g a))
  coherence-dependent-cofork = pr2 k
```

### Homotopies of dependent coforks

A homotopy between dependent coforks is a homotopy between the underlying maps,
together with a coherence condition.

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  { e : cofork f g X} (P : X → UU l4)
  where

  coherence-htpy-dependent-cofork :
    ( k k' : dependent-cofork f g e P) →
    ( K : map-dependent-cofork f g P k ~ map-dependent-cofork f g P k') →
    UU (l1 ⊔ l4)
  coherence-htpy-dependent-cofork k k' K =
    ( a : A) →
    ( ( coherence-dependent-cofork f g P k a) ∙ (K (g a))) ＝
    ( ( ap (tr P (coherence-cofork f g e a)) (K (f a))) ∙
      ( coherence-dependent-cofork f g P k' a))

  htpy-dependent-cofork :
    ( k k' : dependent-cofork f g e P) →
    UU (l1 ⊔ l2 ⊔ l4)
  htpy-dependent-cofork k k' =
    Σ ( map-dependent-cofork f g P k ~ map-dependent-cofork f g P k')
      ( coherence-htpy-dependent-cofork k k')
```

### Obtaining dependent coforks as postcomposition of coforks with dependent maps

One way to obtains dependent coforks is to postcompose the underlying cofork by
a dependent map, according to the diagram

```text
     g
   ----->     e              h
 A -----> B -----> (x : X) -----> (P x)
     f
```

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X)
  where

  dependent-cofork-map :
    { l : Level} {P : X → UU l} → ((x : X) → P x) → dependent-cofork f g e P
  pr1 (dependent-cofork-map h) = h ∘ map-cofork f g e
  pr2 (dependent-cofork-map h) = apd h ∘ coherence-cofork f g e
```

## Properties

### Characterization of identity types of coforks

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  { e : cofork f g X} (P : X → UU l4)
  where

  reflexive-htpy-dependent-cofork :
    ( k : dependent-cofork f g e P) →
    htpy-dependent-cofork f g P k k
  pr1 (reflexive-htpy-dependent-cofork k) = refl-htpy
  pr2 (reflexive-htpy-dependent-cofork k) = right-unit-htpy

  htpy-dependent-cofork-eq :
    ( k k' : dependent-cofork f g e P) →
    ( k ＝ k') → htpy-dependent-cofork f g P k k'
  htpy-dependent-cofork-eq k .k refl = reflexive-htpy-dependent-cofork k

  abstract
    is-torsorial-htpy-dependent-cofork :
      ( k : dependent-cofork f g e P) →
      is-torsorial (htpy-dependent-cofork f g P k)
    is-torsorial-htpy-dependent-cofork k =
      is-torsorial-Eq-structure
        ( ev-pair (coherence-htpy-dependent-cofork f g P k))
        ( is-torsorial-htpy (map-dependent-cofork f g P k))
        ( map-dependent-cofork f g P k , refl-htpy)
        ( is-torsorial-htpy
          ( coherence-dependent-cofork f g P k ∙h refl-htpy))

    is-equiv-htpy-dependent-cofork-eq :
      ( k k' : dependent-cofork f g e P) →
      is-equiv (htpy-dependent-cofork-eq k k')
    is-equiv-htpy-dependent-cofork-eq k =
      fundamental-theorem-id
        ( is-torsorial-htpy-dependent-cofork k)
        ( htpy-dependent-cofork-eq k)

  eq-htpy-dependent-cofork :
    ( k k' : dependent-cofork f g e P) →
    htpy-dependent-cofork f g P k k' → k ＝ k'
  eq-htpy-dependent-cofork k k' =
    map-inv-is-equiv (is-equiv-htpy-dependent-cofork-eq k k')
```

### Dependent coforks on constant type families are equivalent to regular coforks

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) (Y : UU l4)
  where

  compute-dependent-cofork-constant-family :
    dependent-cofork f g e (λ _ → Y) ≃ cofork f g Y
  compute-dependent-cofork-constant-family =
    equiv-tot
      ( λ h →
        equiv-Π-equiv-family
          ( λ a →
            equiv-concat
              ( inv
                ( tr-constant-type-family (coherence-cofork f g e a) (h (f a))))
              ( h (g a))))

  map-compute-dependent-cofork-constant-family :
    dependent-cofork f g e (λ _ → Y) → cofork f g Y
  map-compute-dependent-cofork-constant-family =
    map-equiv compute-dependent-cofork-constant-family

  triangle-compute-dependent-cofork-constant-family :
    coherence-triangle-maps
      ( cofork-map f g e)
      ( map-compute-dependent-cofork-constant-family)
      ( dependent-cofork-map f g e)
  triangle-compute-dependent-cofork-constant-family h =
    eq-htpy-cofork f g
      ( cofork-map f g e h)
      ( map-compute-dependent-cofork-constant-family
        ( dependent-cofork-map f g e h))
      ( ( refl-htpy) ,
        ( right-unit-htpy ∙h
          ( λ a →
            left-transpose-eq-concat _ _ _
              ( inv (apd-constant-type-family h (coherence-cofork f g e a))))))
```

### Dependent coforks are special cases of dependent cocones under spans

The type of dependent coforks on `P` over `e` is equivalent to the type of
[dependent cocones](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
on `P` over a cocone corresponding to `e` via `cocone-codiagonal-cofork`.

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X)
  where

  module _
    { l4 : Level} (P : X → UU l4)
    where

    dependent-cofork-dependent-cocone-codiagonal :
      dependent-cocone
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P) →
      dependent-cofork f g e P
    pr1 (dependent-cofork-dependent-cocone-codiagonal k) =
      vertical-map-dependent-cocone
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P)
        ( k)
    pr2 (dependent-cofork-dependent-cocone-codiagonal k) a =
      inv
        ( ap
          ( tr P (coherence-cofork f g e a))
          ( coherence-square-dependent-cocone
            ( vertical-map-span-cocone-cofork f g)
            ( horizontal-map-span-cocone-cofork f g)
            ( cocone-codiagonal-cofork f g e)
            ( P)
            ( k)
            ( inl a))) ∙
      coherence-square-dependent-cocone
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P)
        ( k)
        ( inr a)

    dependent-cocone-codiagonal-dependent-cofork :
      dependent-cofork f g e P →
      dependent-cocone
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P)
    pr1 (dependent-cocone-codiagonal-dependent-cofork k) =
      map-dependent-cofork f g P k ∘ f
    pr1 (pr2 (dependent-cocone-codiagonal-dependent-cofork k)) =
      map-dependent-cofork f g P k
    pr2 (pr2 (dependent-cocone-codiagonal-dependent-cofork k)) (inl a) =
      refl
    pr2 (pr2 (dependent-cocone-codiagonal-dependent-cofork k)) (inr a) =
      coherence-dependent-cofork f g P k a

    abstract
      is-section-dependent-cocone-codiagonal-dependent-cofork :
        ( ( dependent-cofork-dependent-cocone-codiagonal) ∘
          ( dependent-cocone-codiagonal-dependent-cofork)) ~
        ( id)
      is-section-dependent-cocone-codiagonal-dependent-cofork k =
        eq-htpy-dependent-cofork f g P
          ( dependent-cofork-dependent-cocone-codiagonal
            ( dependent-cocone-codiagonal-dependent-cofork k))
          ( k)
          ( refl-htpy , right-unit-htpy)

      is-retraction-dependent-cocone-codiagonal-dependent-cofork :
        ( ( dependent-cocone-codiagonal-dependent-cofork) ∘
          ( dependent-cofork-dependent-cocone-codiagonal)) ~
        ( id)
      is-retraction-dependent-cocone-codiagonal-dependent-cofork d =
        eq-htpy-dependent-cocone
          ( vertical-map-span-cocone-cofork f g)
          ( horizontal-map-span-cocone-cofork f g)
          ( cocone-codiagonal-cofork f g e)
          ( P)
          ( dependent-cocone-codiagonal-dependent-cofork
            ( dependent-cofork-dependent-cocone-codiagonal d))
          ( d)
          ( inv-htpy
            ( ( coherence-square-dependent-cocone
                ( vertical-map-span-cocone-cofork f g)
                ( horizontal-map-span-cocone-cofork f g)
                ( cocone-codiagonal-cofork f g e)
                ( P)
                ( d)) ∘
              ( inl)) ,
            ( refl-htpy) ,
            ( right-unit-htpy ∙h
              ( λ where
                ( inl a) →
                  inv
                    ( ( ap
                        ( _∙
                          coherence-square-dependent-cocone
                            ( vertical-map-span-cocone-cofork f g)
                            ( horizontal-map-span-cocone-cofork f g)
                            ( cocone-codiagonal-cofork f g e)
                            ( P)
                            ( d)
                            ( inl a))
                        ( ap-id
                          ( inv
                            ( coherence-square-dependent-cocone
                              ( vertical-map-span-cocone-cofork f g)
                              ( horizontal-map-span-cocone-cofork f g)
                              ( cocone-codiagonal-cofork f g e)
                              ( P)
                              ( d)
                              ( inl a))))) ∙
                      ( left-inv
                        ( coherence-square-dependent-cocone
                              ( vertical-map-span-cocone-cofork f g)
                              ( horizontal-map-span-cocone-cofork f g)
                              ( cocone-codiagonal-cofork f g e)
                              ( P)
                              ( d)
                              ( inl a))))
                ( inr a) →
                  ap
                    ( _∙
                      coherence-square-dependent-cocone
                        ( vertical-map-span-cocone-cofork f g)
                        ( horizontal-map-span-cocone-cofork f g)
                        ( cocone-codiagonal-cofork f g e)
                        ( P)
                        ( d)
                        ( inr a))
                    ( inv
                      ( ap-inv
                        ( tr P (coherence-cofork f g e a))
                        ( coherence-square-dependent-cocone
                          ( vertical-map-span-cocone-cofork f g)
                          ( horizontal-map-span-cocone-cofork f g)
                          ( cocone-codiagonal-cofork f g e)
                          ( P)
                          ( d)
                          ( inl a)))))))

    is-equiv-dependent-cofork-dependent-cocone-codiagonal :
      is-equiv dependent-cofork-dependent-cocone-codiagonal
    is-equiv-dependent-cofork-dependent-cocone-codiagonal =
      is-equiv-is-invertible
        ( dependent-cocone-codiagonal-dependent-cofork)
        ( is-section-dependent-cocone-codiagonal-dependent-cofork)
        ( is-retraction-dependent-cocone-codiagonal-dependent-cofork)

    equiv-dependent-cofork-dependent-cocone-codiagonal :
      dependent-cocone
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P) ≃
      dependent-cofork f g e P
    pr1 equiv-dependent-cofork-dependent-cocone-codiagonal =
      dependent-cofork-dependent-cocone-codiagonal
    pr2 equiv-dependent-cofork-dependent-cocone-codiagonal =
      is-equiv-dependent-cofork-dependent-cocone-codiagonal

  triangle-dependent-cofork-dependent-cocone-codiagonal :
    { l4 : Level} (P : X → UU l4) →
    coherence-triangle-maps
      ( dependent-cofork-map f g e)
      ( dependent-cofork-dependent-cocone-codiagonal P)
      ( dependent-cocone-map
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P))
  triangle-dependent-cofork-dependent-cocone-codiagonal P h =
    eq-htpy-dependent-cofork f g P
      ( dependent-cofork-map f g e h)
      ( dependent-cofork-dependent-cocone-codiagonal P
        ( dependent-cocone-map
          ( vertical-map-span-cocone-cofork f g)
          ( horizontal-map-span-cocone-cofork f g)
          ( cocone-codiagonal-cofork f g e)
          ( P)
          ( h)))
      ( refl-htpy ,
        right-unit-htpy)
```
