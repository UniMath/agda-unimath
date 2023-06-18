# Truncated maps

```agda
module foundation-core.truncated-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A map is `k`-truncated if its fibers are `k`-truncated.

## Definition

```agda
module _
  {l1 l2 : Level} (k : 𝕋)
  where

  is-trunc-map : {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
  is-trunc-map f = (y : _) → is-trunc k (fib f y)

  trunc-map : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
  trunc-map A B = Σ (A → B) is-trunc-map

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  map-trunc-map : trunc-map k A B → A → B
  map-trunc-map = pr1

  abstract
    is-trunc-map-map-trunc-map :
      (f : trunc-map k A B) → is-trunc-map k (map-trunc-map f)
    is-trunc-map-map-trunc-map = pr2
```

## Properties

### If a map is `k`-truncated, then it is `k+1`-truncated

```agda
abstract
  is-trunc-map-succ-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {f : A → B} → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-succ-is-trunc-map k is-trunc-f b =
    is-trunc-succ-is-trunc k (is-trunc-f b)
```

### Any contractible map is `k`-truncated

```agda
is-trunc-map-is-contr-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-contr-map f → is-trunc-map k f
is-trunc-map-is-contr-map neg-two-𝕋 H = H
is-trunc-map-is-contr-map (succ-𝕋 k) H =
  is-trunc-map-succ-is-trunc-map k (is-trunc-map-is-contr-map k H)
```

### Any equivalence is `k`-truncated

```agda
is-trunc-map-is-equiv :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-trunc-map k f
is-trunc-map-is-equiv k H =
  is-trunc-map-is-contr-map k (is-contr-map-is-equiv H)
```

### A map is `k+1`-truncated if and only if its action on identifications is `k`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-trunc-map-is-trunc-map-ap :
      ((x y : A) → is-trunc-map k (ap f {x} {y})) → is-trunc-map (succ-𝕋 k) f
    is-trunc-map-is-trunc-map-ap is-trunc-map-ap-f b (pair x p) (pair x' p') =
      is-trunc-equiv k
        ( fib (ap f) (p ∙ (inv p')))
        ( equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
        ( is-trunc-map-ap-f x x' (p ∙ (inv p')))

  abstract
    is-trunc-map-ap-is-trunc-map :
      is-trunc-map (succ-𝕋 k) f → (x y : A) → is-trunc-map k (ap f {x} {y})
    is-trunc-map-ap-is-trunc-map is-trunc-map-f x y p =
      is-trunc-is-equiv' k
        ( pair x p ＝ pair y refl)
        ( eq-fib-fib-ap f x y p)
        ( is-equiv-eq-fib-fib-ap f x y p)
        ( is-trunc-map-f (f y) (pair x p) (pair y refl))
```

### A family of types is a family of `k`-truncated types if and only of the projection map is `k`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1}
  where

  abstract
    is-trunc-map-pr1 :
      {B : A → UU l2} → ((x : A) → is-trunc k (B x)) →
      is-trunc-map k (pr1 {l1} {l2} {A} {B})
    is-trunc-map-pr1 {B} H x =
      is-trunc-equiv k (B x) (equiv-fib-pr1 B x) (H x)

  pr1-trunc-map :
    (B : A → Truncated-Type l2 k) → trunc-map k (Σ A (λ x → pr1 (B x))) A
  pr1 (pr1-trunc-map B) = pr1
  pr2 (pr1-trunc-map B) = is-trunc-map-pr1 (λ x → pr2 (B x))

  abstract
    is-trunc-is-trunc-map-pr1 :
      (B : A → UU l2) → is-trunc-map k (pr1 {l1} {l2} {A} {B}) →
      ((x : A) → is-trunc k (B x))
    is-trunc-is-trunc-map-pr1 B is-trunc-map-pr1 x =
      is-trunc-equiv k (fib pr1 x) (inv-equiv-fib-pr1 B x) (is-trunc-map-pr1 x)
```

### Any map between `k`-truncated types is `k`-truncated

```agda
abstract
  is-trunc-map-is-trunc-domain-codomain :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1}
    {B : UU l2} {f : A → B} → is-trunc k A → is-trunc k B → is-trunc-map k f
  is-trunc-map-is-trunc-domain-codomain k {f = f} is-trunc-A is-trunc-B b =
    is-trunc-Σ is-trunc-A (λ x → is-trunc-Id is-trunc-B (f x) b)
```

### A type family over a `k`-truncated type A is a family of `k`-truncated types if its total space is `k`-truncated

```agda
abstract
  is-trunc-fam-is-trunc-Σ :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → is-trunc k (Σ A B) → (x : A) → is-trunc k (B x)
  is-trunc-fam-is-trunc-Σ k {B = B} is-trunc-A is-trunc-ΣAB x =
    is-trunc-equiv' k
      ( fib pr1 x)
      ( equiv-fib-pr1 B x)
      ( is-trunc-map-is-trunc-domain-codomain k is-trunc-ΣAB is-trunc-A x)
```

### Truncated maps are closed under homotopies

```agda
abstract
  is-trunc-map-htpy :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {f g : A → B} → f ~ g → is-trunc-map k g → is-trunc-map k f
  is-trunc-map-htpy k {A} {B} {f} {g} H is-trunc-g b =
    is-trunc-is-equiv k
      ( Σ A (λ z → g z ＝ b))
      ( fib-triangle f g id H b)
      ( is-fiberwise-equiv-is-equiv-triangle f g id H is-equiv-id b)
      ( is-trunc-g b)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  where

  is-contr-map-htpy : is-contr-map g → is-contr-map f
  is-contr-map-htpy = is-trunc-map-htpy neg-two-𝕋 H

  is-prop-map-htpy : is-prop-map g → is-prop-map f
  is-prop-map-htpy = is-trunc-map-htpy neg-one-𝕋 H
```

### Truncated maps are closed under composition

```agda
abstract
  is-trunc-map-comp :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k (g ∘ h)
  is-trunc-map-comp k g h is-trunc-g is-trunc-h x =
    is-trunc-is-equiv k
        ( Σ (fib g x) (λ t → fib h (pr1 t)))
        ( map-compute-fib-comp g h x)
        ( is-equiv-map-compute-fib-comp g h x)
        ( is-trunc-Σ
          ( is-trunc-g x)
          ( λ t → is-trunc-h (pr1 t)))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B)
  where

  is-contr-map-comp : is-contr-map g → is-contr-map h → is-contr-map (g ∘ h)
  is-contr-map-comp = is-trunc-map-comp neg-two-𝕋 g h

  is-prop-map-comp : is-prop-map g → is-prop-map h → is-prop-map (g ∘ h)
  is-prop-map-comp = is-trunc-map-comp neg-one-𝕋 g h

abstract
  is-trunc-map-comp-htpy :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k f
  is-trunc-map-comp-htpy k f g h H is-trunc-g is-trunc-h =
    is-trunc-map-htpy k H
      ( is-trunc-map-comp k g h is-trunc-g is-trunc-h)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-contr-map-comp-htpy :
    is-contr-map g → is-contr-map h → is-contr-map f
  is-contr-map-comp-htpy = is-trunc-map-comp-htpy neg-two-𝕋 f g h H

  is-prop-map-comp-htpy :
    is-prop-map g → is-prop-map h → is-prop-map f
  is-prop-map-comp-htpy = is-trunc-map-comp-htpy neg-one-𝕋 f g h H
```

### If a composite is truncated, then its right factor is truncated

```agda
abstract
  is-trunc-map-right-factor-htpy :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k f → is-trunc-map k h
  is-trunc-map-right-factor-htpy k {A} f g h H is-trunc-g is-trunc-f b =
    is-trunc-fam-is-trunc-Σ k
      ( is-trunc-g (g b))
      ( is-trunc-is-equiv' k
        ( Σ A (λ z → g (h z) ＝ g b))
        ( map-compute-fib-comp g h (g b))
        ( is-equiv-map-compute-fib-comp g h (g b))
        ( is-trunc-map-htpy k (inv-htpy H) is-trunc-f (g b)))
      ( pair b refl)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-contr-map-right-factor-htpy :
    is-contr-map g → is-contr-map f → is-contr-map h
  is-contr-map-right-factor-htpy =
    is-trunc-map-right-factor-htpy neg-two-𝕋 f g h H

  is-prop-map-right-factor-htpy :
    is-prop-map g → is-prop-map f → is-prop-map h
  is-prop-map-right-factor-htpy =
    is-trunc-map-right-factor-htpy neg-one-𝕋 f g h H

is-trunc-map-right-factor :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) →
  is-trunc-map k g → is-trunc-map k (g ∘ h) → is-trunc-map k h
is-trunc-map-right-factor k {A} g h =
  is-trunc-map-right-factor-htpy k (g ∘ h) g h refl-htpy

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B)
  where

  is-contr-map-right-factor :
    is-contr-map g → is-contr-map (g ∘ h) → is-contr-map h
  is-contr-map-right-factor =
    is-trunc-map-right-factor neg-two-𝕋 g h

  is-prop-map-right-factor :
    is-prop-map g → is-prop-map (g ∘ h) → is-prop-map h
  is-prop-map-right-factor =
    is-trunc-map-right-factor neg-one-𝕋 g h
```

### In a commuting square with the left and right maps equivalences, the top map is truncated if and only if the bottom map is truncated

```agda
module _
  {l1 l2 l3 l4 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (i : C → D)
  (H : coherence-square-maps f g h i)
  where

  is-trunc-map-top-is-trunc-map-bottom-is-equiv :
    is-equiv g → is-equiv h → is-trunc-map k i → is-trunc-map k f
  is-trunc-map-top-is-trunc-map-bottom-is-equiv K L M =
    is-trunc-map-right-factor-htpy k (i ∘ g) h f H
      ( is-trunc-map-is-equiv k L)
      ( is-trunc-map-comp k i g M
        ( is-trunc-map-is-equiv k K))
```

### The map on total spaces induced by a family of truncated maps is truncated

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-trunc-map-tot : ((x : A) → is-trunc-map k (f x)) → is-trunc-map k (tot f)
    is-trunc-map-tot H y =
      is-trunc-equiv k
        ( fib (f (pr1 y)) (pr2 y))
        ( compute-fib-tot f y)
        ( H (pr1 y) (pr2 y))

  abstract
    is-trunc-map-is-trunc-map-tot :
      is-trunc-map k (tot f) → ((x : A) → is-trunc-map k (f x))
    is-trunc-map-is-trunc-map-tot is-trunc-tot-f x z =
      is-trunc-equiv k
        ( fib (tot f) (pair x z))
        ( inv-compute-fib-tot f (pair x z))
        ( is-trunc-tot-f (pair x z))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-contr-map-tot :
      ((x : A) → is-contr-map (f x)) → is-contr-map (tot f)
    is-contr-map-tot =
      is-trunc-map-tot neg-two-𝕋

  abstract
    is-prop-map-tot : ((x : A) → is-prop-map (f x)) → is-prop-map (tot f)
    is-prop-map-tot = is-trunc-map-tot neg-one-𝕋
```

### The functoriality of dependent pair types preserves truncatedness

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  is-trunc-map-map-Σ-map-base :
    (k : 𝕋) {f : A → B} (C : B → UU l3) →
    is-trunc-map k f → is-trunc-map k (map-Σ-map-base f C)
  is-trunc-map-map-Σ-map-base k {f} C H y =
    is-trunc-equiv' k
      ( fib f (pr1 y))
      ( equiv-fib-map-Σ-map-base-fib f C y)
      ( H (pr1 y))

  abstract
    is-prop-map-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) →
      is-prop-map f → is-prop-map (map-Σ-map-base f C)
    is-prop-map-map-Σ-map-base C = is-trunc-map-map-Σ-map-base neg-one-𝕋 C

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  is-trunc-map-map-Σ :
    (k : 𝕋) (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-trunc-map k f → ((x : A) → is-trunc-map k (g x)) →
    is-trunc-map k (map-Σ D f g)
  is-trunc-map-map-Σ k D {f} {g} H K =
    is-trunc-map-comp-htpy k
      ( map-Σ D f g)
      ( map-Σ-map-base f D)
      ( tot g)
      ( triangle-map-Σ D f g)
      ( is-trunc-map-map-Σ-map-base k D H)
      ( is-trunc-map-tot k K)

  module _
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)}
    where

    is-contr-map-map-Σ :
      is-contr-map f → ((x : A) → is-contr-map (g x)) →
      is-contr-map (map-Σ D f g)
    is-contr-map-map-Σ = is-trunc-map-map-Σ neg-two-𝕋 D

    is-prop-map-map-Σ :
      is-prop-map f → ((x : A) → is-prop-map (g x)) → is-prop-map (map-Σ D f g)
    is-prop-map-map-Σ = is-trunc-map-map-Σ neg-one-𝕋 D
```
