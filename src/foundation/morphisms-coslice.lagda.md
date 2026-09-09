# Morphisms in the coslice under a type

```agda
module foundation.morphisms-coslice where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Given a span of maps

```text
      X
     / \
  f /   \ g
   ∨     ∨
  A       B,
```

we define a
{{#concept "morphism" Agda=hom-coslice Disambiguation="in the coslice under a type"}}
between the maps in the coslice category of types to be a map `h : A → B`
together with a coherence triangle `(h ∘ f) ~ g`:

```text
      X
     / \
  f /   \ g
   ∨     ∨
  A ----> B.
      h
```

## Definition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : X → A) (g : X → B)
  where

  hom-coslice = Σ (A → B) (λ h → h ∘ f ~ g)

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {f : X → A} {g : X → B}
  where

  map-hom-coslice : hom-coslice f g → A → B
  map-hom-coslice = pr1

  triangle-hom-coslice :
    (h : hom-coslice f g) → map-hom-coslice h ∘ f ~ g
  triangle-hom-coslice = pr2
```

## Properties

### Characterizing the identity type of coslice morphisms

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {f : X → A} {g : X → B}
  where

  coherence-htpy-hom-coslice :
    (h k : hom-coslice f g) →
    map-hom-coslice h ~ map-hom-coslice k → UU (l1 ⊔ l3)
  coherence-htpy-hom-coslice h k H =
    coherence-triangle-homotopies
      ( triangle-hom-coslice h)
      ( triangle-hom-coslice k)
      ( H ·r f)

  htpy-hom-coslice :
    (h k : hom-coslice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-coslice h k =
    Σ ( map-hom-coslice h ~ map-hom-coslice k)
      ( coherence-htpy-hom-coslice h k)

  extensionality-hom-coslice :
    (h k : hom-coslice f g) → (h ＝ k) ≃ htpy-hom-coslice h k
  extensionality-hom-coslice (h , H) =
    extensionality-Σ
      ( λ {h' : A → B} (H' : h' ∘ f ~ g) (K : h ~ h') → H ~ ((K ·r f) ∙h H'))
      ( refl-htpy)
      ( refl-htpy)
      ( λ h' → equiv-funext)
      ( λ H' → equiv-funext)

  eq-htpy-hom-coslice :
    ( h k : hom-coslice f g)
    ( H : map-hom-coslice h ~ map-hom-coslice k)
    ( K : coherence-htpy-hom-coslice h k H) →
    h ＝ k
  eq-htpy-hom-coslice h k H K =
    map-inv-equiv (extensionality-hom-coslice h k) (H , K)
```
