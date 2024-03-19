# Function types

```agda
module foundation.function-types where

open import foundation-core.function-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-dependent-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopy-induction
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation.commuting-triangles-of-identifications
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Properties

### Transport in a family of function types

Consider two type families `B` and `C` over `A`, an identification `p : x ＝ y`
in `A` and a function `f : B x → C x`. Then there is an identification

```text
  tr (λ x → B x → C x) p f ＝ tr C p ∘ f ∘ tr B (inv p)
```

From this identification we obtain a homotopy witnessing that the square

```text
        tr B p
   B a --------> B b
    |             |
  f |             | tr (λ x → B x → C x) p f
    ∨             ∨
   C a --------> C b
        tr C p
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {x y : A} (B : A → UU l2) (C : A → UU l3)
  where

  tr-function-type :
    (p : x ＝ y) (f : B x → C x) →
    tr (λ a → B a → C a) p f ＝ tr C p ∘ f ∘ tr B (inv p)
  tr-function-type refl f = refl

  coherence-square-tr-function-type :
    (p : x ＝ y) (f : B x → C x) →
    coherence-square-maps
      ( tr B p)
      ( f)
      ( tr (λ a → B a → C a) p f)
      ( tr C p)
  coherence-square-tr-function-type refl f = refl-htpy
```

### Dependent identifications in a family of function types

Consider two type families `B` and `C` over `A`, an identification `p : x ＝ y`
in `A` and two functions

```text
  f : B x → C x
  g : B y → C y.
```

Then the type of dependent identifications from `f` to `g` over `p` can be
computed as

```text
  (tr C p ∘ f ~ g ∘ tr B p) ≃ dependent-identification (x ↦ B x → C x) f g.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {x y : A} (B : A → UU l2) (C : A → UU l3)
  where

  compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    coherence-square-maps (tr B p) f g (tr C p) ≃
    dependent-identification (λ a → B a → C a) p f g
  compute-dependent-identification-function-type refl f g =
    inv-equiv equiv-funext

  map-compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    coherence-square-maps (tr B p) f g (tr C p) →
    dependent-identification (λ a → B a → C a) p f g
  map-compute-dependent-identification-function-type p f g =
    map-equiv (compute-dependent-identification-function-type p f g)
```

### Transport in a family of function types with fixed codomain

Consider an identification `p : a ＝ b` in a type `A`, a type family `B : A → 𝒰`, and a function `f : B a → C`. Then the triangle of maps

```text
       tr B p
  B a --------> B b
     \         /
      \       /
     f \     / tr (x ↦ B x → C) p f
        \   /
         ∨ ∨
          X
```

commutes by a homotopy `H : f ~ tr (x ↦ B x → C) p f ∘ tr B p`.

Moreover, given a family `f : (x : A) → B x → C` of functions with fixed codomain `C`, we can say more about how the identifications `H y` constructed above fit together: Each identification `H y` fits in a commuting triangle of identifications

```text
                            H y
                   f a y --------> tr (x ↦ B x → C) p f (tr B p y)
                        \         /
                         \       /
  ap (ind-Σ f) (p , refl) \     / htpy-eq (apd f p) (tr B p y)
                           \   /
                            ∨ ∨
                      f b (tr B p y).
```

Similarly, given a map `f : Σ A B → C` we obtain a commuting triangle of identifications

```text
                    H y
       f (a , y) --------> tr (x ↦ B x → C) (ev-pair f a) (tr B p y)
                \         /
                 \       /
  ap f (p , refl) \     / htpy-eq (apd (ev-pair f) p) (tr B p y)
                   \   /
                    ∨ ∨
               f (b , tr B p y).
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {a b : A} (B : A → UU l2) (C : UU l3)
  where

  compute-tr-function-type-fixed-domain :
    (p : a ＝ b) (f : B a → C) → f ＝ tr (λ x → B x → C) p f ∘ tr B p
  compute-tr-function-type-fixed-domain refl f = refl

  htpy-compute-tr-function-type-fixed-domain :
    (p : a ＝ b) (f : B a → C) →
    coherence-triangle-maps f (tr (λ x → B x → C) p f) (tr B p)
  htpy-compute-tr-function-type-fixed-domain p f =
    htpy-eq (compute-tr-function-type-fixed-domain p f)

  coherence-triangle-compute-tr-function-type-fixed-domain :
    (p : a ＝ b) (f : (x : A) → B x → C) (y : B a) →
    coherence-triangle-identifications
      ( ap (ind-Σ f) (eq-pair-Σ p refl))
      ( htpy-eq (apd f p) (tr B p y))
      ( htpy-compute-tr-function-type-fixed-domain p (f a) y)
  coherence-triangle-compute-tr-function-type-fixed-domain refl f y =
    refl

  coherence-triangle-compute-tr-function-type-fixed-domain' :
    (p : a ＝ b) (f : Σ A B → C) (y : B a) →
    coherence-triangle-identifications
      ( ap f (eq-pair-Σ p refl))
      ( htpy-eq (apd (ev-pair f) p) (tr B p y))
      ( htpy-compute-tr-function-type-fixed-domain p (ev-pair f a) y)
  coherence-triangle-compute-tr-function-type-fixed-domain' refl f y =
    refl
```

### Dependent identifications in a family of function types with fixed codomain

Consider an identification `p : a ＝ b` in a type `A`, a type family `B : A → 𝒰`, a function `f : B a → C` and a function `g : B b → C`. Then we have an equivalence

```text
  α⁻¹ p : dependent-identification (x ↦ B x → C) p f g ≃ (f ~ g ∘ tr B p)
```

with inverse

```text
  α p : (f ~ g ∘ tr B p) ≃ dependent-identification (x ↦ B x → C) p f g.
```

Note that it is conventional in agda-unimath to direct computations of types from the computed value to the type being computed. The family of equivalences `α⁻¹` is constructed by identification elimination. In the case where `p ≐ refl` the equivalence is given by function extensionality.

Given an identification `p : a ＝ b` and a map `f : Σ A B → C`, we can compute `α p` as follows:

```text
  α p (λ y → ap f (eq-pair-Σ p refl)) ＝ apd (ev-pair f) p
```

Furthermore, given an identification `p : a ＝ b` and a family of maps `f : (x : A) → B x → C` with fixed codomain `C`, we can compute `α⁻¹ p` to the action on identifications of the map `ind-Σ f : Σ A B → C`:

```text
  α⁻¹ p (apd f p) y ＝ ap (ind-Σ f) (eq-pair-Σ p refl).
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {a b : A} (B : A → UU l2) (C : UU l3)
  where

  inv-compute-dependent-identification-function-type-fixed-codomain :
    (p : a ＝ b) (f : B a → C) (g : B b → C) →
    dependent-identification (λ x → B x → C) p f g ≃
    ((y : B a) → f y ＝ g (tr B p y))
  inv-compute-dependent-identification-function-type-fixed-codomain refl f g =
    equiv-funext

  map-inv-compute-dependent-identification-function-type-fixed-codomain :
    (p : a ＝ b) {f : B a → C} {g : B b → C} →
    dependent-identification (λ x → B x → C) p f g →
    ((y : B a) → f y ＝ g (tr B p y))
  map-inv-compute-dependent-identification-function-type-fixed-codomain p =
    map-equiv
      ( inv-compute-dependent-identification-function-type-fixed-codomain p _ _)

  compute-dependent-identification-function-type-fixed-codomain :
    (p : a ＝ b) (f : B a → C) (g : B b → C) →
    ((y : B a) → f y ＝ g (tr B p y)) ≃
    dependent-identification (λ x → B x → C) p f g
  compute-dependent-identification-function-type-fixed-codomain p f g =
    inv-equiv
      ( inv-compute-dependent-identification-function-type-fixed-codomain p f g)

  map-compute-dependent-identification-function-type-fixed-codomain :
    (p : a ＝ b) {f : B a → C} {g : B b → C} →
    ((y : B a) → f y ＝ g (tr B p y)) →
    dependent-identification (λ x → B x → C) p f g
  map-compute-dependent-identification-function-type-fixed-codomain p {f} {g} =
    map-equiv
      ( compute-dependent-identification-function-type-fixed-codomain p f g)

  compute-inv-compute-dependent-identification-function-type-fixed-codomain :
    (p : a ＝ b) (f : (x : A) → B x → C) (y : B a) →
    map-inv-compute-dependent-identification-function-type-fixed-codomain p
      ( apd f p)
      ( y) ＝
    ap (ind-Σ f) (eq-pair-Σ p refl)
  compute-inv-compute-dependent-identification-function-type-fixed-codomain
    refl f =
    refl-htpy

  compute-compute-dependent-identification-function-type-fixed-codomain :
    (p : a ＝ b) (f : Σ A B → C) →
    map-compute-dependent-identification-function-type-fixed-codomain p
      (λ y → ap f (eq-pair-Σ p refl)) ＝
    apd (ev-pair f) p
  compute-compute-dependent-identification-function-type-fixed-codomain
    refl f =
    eq-htpy-refl-htpy _
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
            ( λ k l s → inv-equiv (equiv-funext)))) ∙
        ( eq-htpy-refl-htpy (h (i s))))
```

## See also

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}
