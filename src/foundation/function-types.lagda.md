# Function types

```agda
module foundation.function-types where

open import foundation-core.function-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-pentagons-of-identifications
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopy-induction
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Properties

### Associativity of function composition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (h : C → D) (g : B → C) (f : A → B)
  where

  associative-comp : (h ∘ g) ∘ f ＝ h ∘ (g ∘ f)
  associative-comp = refl
```

### The Mac Lane pentagon for function composition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {E : UU l5}
  {f : A → B} {g : B → C} {h : C → D} {i : D → E}
  where

  mac-lane-pentagon-comp :
    let α₁ = (ap (_∘ f) (associative-comp i h g))
        α₂ = (associative-comp i (h ∘ g) f)
        α₃ = (ap (i ∘_) (associative-comp h g f))
        α₄ = (associative-comp (i ∘ h) g f)
        α₅ = (associative-comp i h (g ∘ f))
    in
      coherence-pentagon-identifications α₁ α₄ α₂ α₅ α₃
  mac-lane-pentagon-comp = refl
```

### Transport in a family of function types

Consider two type families `B` and `C` over `A`, an identification `p : x ＝ y`
in `A` and two functions

```text
  f : B x → C x
  g : B y → C y.
```

Then the type of dependent identifications from `f` to `g` over `p` can be
computed as

```text
  ((b : B x) → tr C p (f b) ＝ g (tr B p b))
  ≃ dependent-identification (x ↦ B x → C x) f g.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {x y : A} (B : A → UU l2) (C : A → UU l3)
  where

  tr-function-type :
    (p : x ＝ y) (f : B x → C x) →
    tr (λ a → B a → C a) p f ＝ (tr C p ∘ (f ∘ tr B (inv p)))
  tr-function-type refl f = refl

  compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ( (b : B x) → tr C p (f b) ＝ g (tr B p b)) ≃
    ( dependent-identification (λ a → B a → C a) p f g)
  compute-dependent-identification-function-type refl f g =
    inv-equiv equiv-funext

  map-compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ((b : B x) → tr C p (f b) ＝ g (tr B p b)) →
    dependent-identification (λ a → B a → C a) p f g
  map-compute-dependent-identification-function-type p f g =
    map-equiv (compute-dependent-identification-function-type p f g)
```

### Transport in a family of function types with fixed codomain

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {x y : A} (B : A → UU l2) (C : UU l3)
  where

  tr-function-type-fixed-codomain :
    (p : x ＝ y) (f : B x → C) →
    tr (λ a → B a → C) p f ＝ f ∘ tr B (inv p)
  tr-function-type-fixed-codomain refl f = refl

  compute-dependent-identification-function-type-fixed-codomain :
    (p : x ＝ y) (f : B x → C) (g : B y → C) →
    ((b : B x) → f b ＝ g (tr B p b)) ≃
    dependent-identification (λ a → B a → C) p f g
  compute-dependent-identification-function-type-fixed-codomain refl f g =
    inv-equiv equiv-funext

  map-compute-dependent-identification-function-type-fixed-codomain :
    (p : x ＝ y) (f : B x → C) (g : B y → C) →
    ((b : B x) → f b ＝ g (tr B p b)) →
    dependent-identification (λ a → B a → C) p f g
  map-compute-dependent-identification-function-type-fixed-codomain p f g =
    map-equiv
      ( compute-dependent-identification-function-type-fixed-codomain p f g)
```

### Transport in a family of function types with fixed domain

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {x y : A} (B : UU l2) (C : A → UU l3)
  where

  tr-function-type-fixed-domain :
    (p : x ＝ y) (f : B → C x) →
    tr (λ a → B → C a) p f ＝ tr C p ∘ f
  tr-function-type-fixed-domain refl f = refl
```

### Relation between `compute-dependent-identification-function-type` and `preserves-tr`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {i0 i1 : I} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i)
  where

  preserves-tr-apd-function :
    (p : i0 ＝ i1) (a : A i0) →
    map-inv-equiv
      ( compute-dependent-identification-function-type A B p (f i0) (f i1))
      ( apd f p) a ＝
    inv-htpy (preserves-tr f p) a
  preserves-tr-apd-function refl = refl-htpy
```

### Computation of dependent identifications of functions over homotopies

```agda
module _
  { l1 l2 l3 l4 : Level}
  { S : UU l1} {X : UU l2} {P : X → UU l3} (Y : UU l4)
  { i : S → X}
  where

  equiv-htpy-dependent-function-dependent-identification-function-type :
    { j : S → X} (H : i ~ j) →
    ( k : (s : S) → P (i s) → Y)
    ( l : (s : S) → P (j s) → Y) →
    ( s : S) →
    ( k s ~ (l s ∘ tr P (H s))) ≃
    ( dependent-identification
      ( λ x → P x → Y)
      ( H s)
      ( k s)
      ( l s))
  equiv-htpy-dependent-function-dependent-identification-function-type =
    ind-htpy i
      ( λ j H →
        ( k : (s : S) → P (i s) → Y) →
        ( l : (s : S) → P (j s) → Y) →
        ( s : S) →
        ( k s ~ (l s ∘ tr P (H s))) ≃
        ( dependent-identification
          ( λ x → P x → Y)
          ( H s)
          ( k s)
          ( l s)))
      ( λ k l s → inv-equiv (equiv-funext))

  compute-equiv-htpy-dependent-function-dependent-identification-function-type :
    { j : S → X} (H : i ~ j) →
    ( h : (x : X) → P x → Y) →
    ( s : S) →
    ( map-equiv
      ( equiv-htpy-dependent-function-dependent-identification-function-type H
        ( h ∘ i)
        ( h ∘ j)
        ( s))
      ( λ t → ap (ind-Σ h) (eq-pair-Σ (H s) refl))) ＝
    ( apd h (H s))
  compute-equiv-htpy-dependent-function-dependent-identification-function-type =
    ind-htpy i
      ( λ j H →
        ( h : (x : X) → P x → Y) →
        ( s : S) →
        ( map-equiv
          ( equiv-htpy-dependent-function-dependent-identification-function-type
            ( H)
            ( h ∘ i)
            ( h ∘ j)
            ( s))
          ( λ t → ap (ind-Σ h) (eq-pair-Σ (H s) refl))) ＝
        ( apd h (H s)))
      ( λ h s →
        ( ap
          ( λ f → map-equiv (f (h ∘ i) (h ∘ i) s) refl-htpy)
          ( compute-ind-htpy i
            ( λ j H →
              ( k : (s : S) → P (i s) → Y) →
              ( l : (s : S) → P (j s) → Y) →
              ( s : S) →
              ( k s ~ (l s ∘ tr P (H s))) ≃
              ( dependent-identification
                ( λ x → P x → Y)
                ( H s)
                ( k s)
                ( l s)))
            ( λ k l s → inv-equiv equiv-funext))) ∙
        ( eq-htpy-refl-htpy (h (i s))))
```

## See also

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}
