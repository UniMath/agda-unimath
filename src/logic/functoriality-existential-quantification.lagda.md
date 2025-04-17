# Functoriality of existential quantification

```agda
module logic.functoriality-existential-quantification where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.universe-levels
```

</details>

## Idea

Any map `f : A → B` and any family of maps `g : (x : A) → C x → D (f x)`
together induce a map

```text
  map-exists D f g : ∃ A C → ∃ B D.
```

We call this the
{{#concept "functorial action" Disambiguation="of existential quantification" Agda=map-exists}}
of [existential quantification](foundation.existential-quantification.md).

## Definitions

### The functorial action of existential quantification

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  where

  map-exists :
    (f : A → C) (g : (x : A) → B x → D (f x)) →
    exists-structure A B → exists-structure C D
  map-exists f g =
    elim-exists (exists-structure-Prop C D) (λ x y → intro-exists (f x) (g x y))
```

### The binary functorial action of existential quantification

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : A → UU l2}
  {C : UU l3} {D : C → UU l4}
  {E : UU l5} (F : E → UU l6)
  where

  map-binary-exists :
    (f : A → C → E) (g : (x : A) (y : C) → B x → D y → F (f x y)) →
    exists-structure A B →
    exists-structure C D →
    exists-structure E F
  map-binary-exists f g |ab| =
    elim-exists
      ( exists-structure-Prop E F)
      ( λ c d → map-exists F (λ a → f a c) (λ a b → g a c b d) |ab|)
```

### The ternary functorial action of existential quantification

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : A → UU l2}
  {C : UU l3} {D : C → UU l4}
  {E : UU l5} {F : E → UU l6}
  {G : UU l7} (H : G → UU l8)
  where

  map-ternary-exists :
    (f : A → C → E → G)
    (g : (x : A) (y : C) (z : E) → B x → D y → F z → H (f x y z)) →
    exists-structure A B →
    exists-structure C D →
    exists-structure E F →
    exists-structure G H
  map-ternary-exists f g |ab| |cd| =
    elim-exists
      ( exists-structure-Prop G H)
      ( λ e f' →
        map-binary-exists H
          ( λ a c → f a c e)
          ( λ a c b d → g a c e b d f')
          ( |ab|)
          ( |cd|))
```

### The functorial action of existential quantification on families of maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  map-tot-exists :
    (g : (x : A) → B x → C x) → exists-structure A B → exists-structure A C
  map-tot-exists g = map-exists C id g
```

### The functorial action of existential quantification on families of logical equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  iff-tot-exists :
    (g : (x : A) → B x ↔ C x) → exists-structure A B ↔ exists-structure A C
  pr1 (iff-tot-exists g) = map-tot-exists (forward-implication ∘ g)
  pr2 (iff-tot-exists g) = map-tot-exists (backward-implication ∘ g)
```

### The functorial action of existential quantification on maps of the base

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  map-exists-map-base :
    (f : A → B) → exists-structure A (C ∘ f) → exists-structure B C
  map-exists-map-base f = map-exists C f (λ _ → id)
```
