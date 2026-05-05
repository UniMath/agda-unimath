# Lifts of maps

```agda
module orthogonal-factorization-systems.lifts-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.dependent-products-truncated-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.small-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
```

</details>

## Idea

A **lift** of a map `f : X → B` along a map `i : A → B` is a map `g : X → A`
such that the composition `i ∘ g` is `f`.

```text
           A
          ∧|
        /  i
      g    |
    /      ∨
  X - f -> B
```

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-lift-of-map : {X : UU l3} → (X → B) → (X → A) → UU (l2 ⊔ l3)
  is-lift-of-map f g = (f ~ i ∘ g)

  lift-map : {X : UU l3} → (X → B) → UU (l1 ⊔ l2 ⊔ l3)
  lift-map {X} f = Σ (X → A) (is-lift-of-map f)

  total-lift-map : (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-lift-map X = Σ (X → B) lift-map

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {X : UU l3} {f : X → B}
  where

  map-lift-map : lift-map i f → X → A
  map-lift-map = pr1

  is-lift-map-lift-map :
    (l : lift-map i f) → is-lift-of-map i f (map-lift-map l)
  is-lift-map-lift-map = pr2
```

## Operations

### Vertical composition of lifts of maps

```text
           A
          ∧|
        /  i
      g    |
    /      ∨
  X - f -> B
    \      |
      h    j
       \   |
         ∨ ∨
           C
```

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  {i : A → B} {j : B → C} {f : X → B} {h : X → C} {g : X → A}
  where

  is-lift-of-map-comp-vertical :
    is-lift-of-map i f g → is-lift-of-map j h f → is-lift-of-map (j ∘ i) h g
  is-lift-of-map-comp-vertical F H x = H x ∙ ap j (F x)
```

### Horizontal composition of lifts of maps

```text
  A - f -> B - g -> C
    \      |      /
      h    i    j
        \  |  /
         ∨ ∨ ∨
           X
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  {f : A → B} {g : B → C} {h : A → X} {i : B → X} {j : C → X}
  where

  is-lift-of-map-comp-horizontal :
    is-lift-of-map j i g → is-lift-of-map i h f → is-lift-of-map j h (g ∘ f)
  is-lift-of-map-comp-horizontal J I x = I x ∙ J (f x)
```

## Left whiskering of lifts of maps

```text
           A
          ∧|
        /  i
      g    |
    /      ∨
  X - f -> B - h -> S
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {S : UU l4}
  {i : A → B} {f : X → B} {g : X → A}
  where

  is-lift-of-map-left-whisker :
    (h : B → S) → is-lift-of-map i f g → is-lift-of-map (h ∘ i) (h ∘ f) g
  is-lift-of-map-left-whisker h H x = ap h (H x)
```

## Right whiskering of lifts of maps

```text
                    A
                   ∧|
                 /  i
               g    |
             /      ∨
  S - h -> X - f -> B
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {S : UU l4}
  {i : A → B} {f : X → B} {g : X → A}
  where

  is-lift-of-map-right-whisker :
    is-lift-of-map i f g → (h : S → X) → is-lift-of-map i (f ∘ h) (g ∘ h)
  is-lift-of-map-right-whisker H h s = H (h s)
```

## Properties

### Characterizing identifications of lifts of maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {X : UU l3} (f : X → B)
  where

  coherence-htpy-lift-map :
    (l l' : lift-map i f) → map-lift-map i l ~ map-lift-map i l' → UU (l2 ⊔ l3)
  coherence-htpy-lift-map l l' K =
    is-lift-map-lift-map i l ∙h (i ·l K) ~ is-lift-map-lift-map i l'

  htpy-lift-map : (l l' : lift-map i f) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-lift-map l l' =
    Σ ( map-lift-map i l ~ map-lift-map i l')
      ( coherence-htpy-lift-map l l')

  refl-htpy-lift-map : (l : lift-map i f) → htpy-lift-map l l
  pr1 (refl-htpy-lift-map l) = refl-htpy
  pr2 (refl-htpy-lift-map l) = right-unit-htpy

  htpy-eq-lift-map : (l l' : lift-map i f) → l ＝ l' → htpy-lift-map l l'
  htpy-eq-lift-map l .l refl = refl-htpy-lift-map l

  is-torsorial-htpy-lift-map :
    (l : lift-map i f) → is-torsorial (htpy-lift-map l)
  is-torsorial-htpy-lift-map l =
    is-torsorial-Eq-structure
      (is-torsorial-htpy (map-lift-map i l))
      (map-lift-map i l , refl-htpy)
      (is-torsorial-htpy (is-lift-map-lift-map i l ∙h refl-htpy))

  is-equiv-htpy-eq-lift-map :
    (l l' : lift-map i f) → is-equiv (htpy-eq-lift-map l l')
  is-equiv-htpy-eq-lift-map l =
    fundamental-theorem-id (is-torsorial-htpy-lift-map l) (htpy-eq-lift-map l)

  extensionality-lift-map :
    (l l' : lift-map i f) → (l ＝ l') ≃ (htpy-lift-map l l')
  pr1 (extensionality-lift-map l l') = htpy-eq-lift-map l l'
  pr2 (extensionality-lift-map l l') = is-equiv-htpy-eq-lift-map l l'

  eq-htpy-lift-map : (l l' : lift-map i f) → htpy-lift-map l l' → l ＝ l'
  eq-htpy-lift-map l l' = map-inv-equiv (extensionality-lift-map l l')
```

### The total type of lifts of maps is equivalent to `X → A`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B) (X : UU l3)
  where

  inv-compute-total-lift-map : total-lift-map i X ≃ (X → A)
  inv-compute-total-lift-map =
    ( right-unit-law-Σ-is-contr (λ f → is-torsorial-htpy' (i ∘ f))) ∘e
    ( equiv-left-swap-Σ)

  compute-total-lift-map : (X → A) ≃ total-lift-map i X
  compute-total-lift-map = inv-equiv inv-compute-total-lift-map

  is-small-total-lift-map : is-small (l1 ⊔ l3) (total-lift-map i X)
  pr1 (is-small-total-lift-map) = X → A
  pr2 (is-small-total-lift-map) = inv-compute-total-lift-map
```

### The truncation level of the type of lifts is bounded by the truncation level of the codomains

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-trunc-is-lift-of-map :
    {X : UU l3} (f : X → B) →
    is-trunc (succ-𝕋 k) B → (g : X → A) → is-trunc k (is-lift-of-map i f g)
  is-trunc-is-lift-of-map f is-trunc-B g =
    is-trunc-Π k (λ x → is-trunc-B (f x) (i (g x)))

  is-trunc-lift-map :
    {X : UU l3} (f : X → B) →
    is-trunc k A → is-trunc (succ-𝕋 k) B → is-trunc k (lift-map i f)
  is-trunc-lift-map f is-trunc-A is-trunc-B =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-A)
      ( is-trunc-is-lift-of-map f is-trunc-B)

  is-trunc-total-lift-map :
    (X : UU l3) → is-trunc k A → is-trunc k (total-lift-map i X)
  is-trunc-total-lift-map X is-trunc-A =
    is-trunc-equiv' k
      ( X → A)
      ( compute-total-lift-map i X)
      ( is-trunc-function-type k is-trunc-A)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-contr-is-lift-of-map :
    {X : UU l3} (f : X → B) →
    is-prop B → (g : X → A) → is-contr (is-lift-of-map i f g)
  is-contr-is-lift-of-map f is-prop-B g =
    is-contr-Π (λ x → is-prop-B (f x) (i (g x)))

  is-prop-is-lift-of-map :
    {X : UU l3} (f : X → B) →
    is-set B → (g : X → A) → is-prop (is-lift-of-map i f g)
  is-prop-is-lift-of-map f is-set-B g =
    is-prop-Π (λ x → is-set-B (f x) (i (g x)))
```

## See also

- [`orthogonal-factorization-systems.extensions-maps`](orthogonal-factorization-systems.extensions-maps.md)
  for the dual notion.
