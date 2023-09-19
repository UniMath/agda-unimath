# Coforks

```agda
module synthetic-homotopy-theory.coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.function-types
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies
```

</details>

## Idea

A **cofork** of a parallel pair `f, g : A → B` with vertext `X` is a map
`e : B → X` together with a [homotopy](foundation.homotopies.md)
`e ∘ f ~ e ∘ g`. The name comes from the diagram

```text
     g
   ----->     e
 A -----> B -----> X
     f
```

which looks like a fork if you flip the arrows, hence a cofork.


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

  is-contr-total-htpy-cofork :
    ( e : cofork f g X) → is-contr (Σ (cofork f g X) (htpy-cofork f g e))
  is-contr-total-htpy-cofork e =
    is-contr-total-Eq-structure
      ( ev-pair (coherence-htpy-cofork f g e))
      ( is-contr-total-htpy (map-cofork f g e))
      ( (map-cofork f g e) , refl-htpy)
      ( is-contr-is-equiv'
        ( Σ ( map-cofork f g e ∘ f ~ map-cofork f g e ∘ g)
            ( λ K → coherence-cofork f g e ~ K))
        ( tot (λ K M → right-unit-htpy ∙h M))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ H → is-equiv-concat-htpy right-unit-htpy H))
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
