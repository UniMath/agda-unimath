# Precomposition of dependent functions

```agda
module foundation.precomposition-dependent-functions where

open import foundation-core.precomposition-dependent-functions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-homotopies
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.function-extensionality
open import foundation.sections
open import foundation.transport-along-homotopies
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Properties

### Computations of the fibers of `precomp-Π`

The fiber of `- ∘ f : ((b : B) → U b) → ((a : A) → U (f a))` at
`g ∘ f : (b : B) → U b` is equivalent to the type of maps `h : (b : B) → U b`
equipped with a homotopy witnessing that the square

```text
        f
    A -----> B
    |        |
  f |        | h
    ∨        ∨
    B ---> U ∘ f
        g
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (U : B → UU l3)
  where

  compute-extension-fiber-precomp-Π' :
    (g : (a : A) → U (f a)) →
    fiber (precomp-Π f U) g ≃
    Σ ((b : B) → U b) (λ h → (a : A) → (h ∘ f) a ＝ g a)
  compute-extension-fiber-precomp-Π' g =
    equiv-tot (λ h → equiv-funext)

  compute-extension-fiber-precomp-Π :
    (g : (a : A) → U (f a)) →
    fiber (precomp-Π f U) g ≃ Σ ((b : B) → U b) (λ h → g ~ h ∘ f)
  compute-extension-fiber-precomp-Π g =
    equiv-tot (λ h → equiv-funext) ∘e equiv-fiber (precomp-Π f U) g

  compute-fiber-precomp-Π :
    (g : (b : B) → U b) →
    fiber (precomp-Π f U) (g ∘ f) ≃ Σ ((b : B) → U b) (λ h → g ∘ f ~ h ∘ f)
  compute-fiber-precomp-Π g =
    compute-extension-fiber-precomp-Π (g ∘ f)

  compute-total-fiber-precomp-Π :
    Σ ((b : B) → U b) (λ g → fiber (precomp-Π f U) (g ∘ f)) ≃
    Σ ((b : B) → U b) (λ u → Σ ((b : B) → U b) (λ v → u ∘ f ~ v ∘ f))
  compute-total-fiber-precomp-Π = equiv-tot compute-fiber-precomp-Π

  diagonal-into-fibers-precomp-Π :
    ((b : B) → U b) → Σ ((b : B) → U b) (λ g → fiber (precomp-Π f U) (g ∘ f))
  diagonal-into-fibers-precomp-Π = map-section-family (λ g → (g , refl))
```

- In
  [`foundation.universal-property-family-of-fibers-of-maps`](foundation.universal-property-family-of-fibers-of-maps.md)
  we compute the fiber family of dependent precomposition maps as a dependent
  product
  ```text
    dependent-product-characterization-fiber-precomp-Π :
      fiber (precomp-Π f U) g ≃
      ( (b : B) →
        Σ (u : U b),
          (((a , p) : fiber f b) → dependent-identification U p (g a) u)).
  ```

### The action of dependent precomposition on homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : f ~ g) (C : B → UU l3) (h : (y : B) → C y)
  where

  eq-htpy-precomp-Π : (λ x → tr C (H x) (precomp-Π f C h x)) ＝ precomp-Π g C h
  eq-htpy-precomp-Π = eq-htpy (htpy-htpy-precomp-Π H C h)

  htpy-precomp-Π :
    dependent-identification
      ( λ v → (a : A) → C (v a))
      ( eq-htpy H)
      ( precomp-Π f C h)
      ( precomp-Π g C h)
  htpy-precomp-Π =
    compute-tr-htpy (λ _ → C) H (precomp-Π f C h) ∙ eq-htpy-precomp-Π

  eq-htpy-precomp-Π' :
    precomp-Π f C h ＝ (λ x → inv-tr C (H x) (precomp-Π g C h x))
  eq-htpy-precomp-Π' = eq-htpy (htpy-htpy-precomp-Π' H C h)

  htpy-precomp-Π' :
    dependent-identification'
      ( λ v → (a : A) → C (v a))
      ( eq-htpy H)
      ( precomp-Π f C h)
      ( precomp-Π g C h)
  htpy-precomp-Π' =
    eq-htpy-precomp-Π' ∙ inv (compute-inv-tr-htpy (λ _ → C) H (precomp-Π g C h))
```

### Equivalences induce an equivalence from the type of homotopies between two dependent functions to the type of homotopies between their precomposites

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1}
  where

  equiv-htpy-precomp-htpy-Π :
    {B : UU l2} {C : B → UU l3} (f g : (b : B) → C b) (e : A ≃ B) →
    (f ~ g) ≃ (f ∘ map-equiv e ~ g ∘ map-equiv e)
  equiv-htpy-precomp-htpy-Π f g e =
    equiv-precomp-Π e (eq-value f g)
```

### The action on identifications of precomposition of dependent functions

Consider a map `f : A → B` and two dependent functions `g h : (x : B) → C x`.
Then the square

```text
                     ap (precomp-Π f C)
       (g ＝ h) ---------------------------> (g ∘ f ＝ h ∘ f)
          |                                         |
  htpy-eq |                                         | htpy-eq
          ∨                                         ∨
       (g ~ h) ----------------------------> (g ∘ f ~ h ∘ f)
                precomp-Π f (eq-value g h)
```

[commutes](foundation-core.commuting-squares-of-maps.md).

Similarly, the map `ap (precomp-Π f C)` fits in a commuting square

```text
                precomp-Π f (eq-value g h)
       (g ~ h) ----------------------------> (g ∘ f ~ h ∘ f)
          |                                         |
  eq-htpy |                                         | eq-htpy
          ∨                                         ∨
       (g ＝ h) ---------------------------> (g ∘ f ＝ h ∘ f).
                     ap (precomp-Π f C)
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) {C : B → UU l3}
  {g h : (b : B) → C b}
  where

  coherence-htpy-eq-ap-precomp-Π :
    coherence-square-maps
      ( ap (precomp-Π f C) {g} {h})
      ( htpy-eq)
      ( htpy-eq)
      ( precomp-Π f (eq-value g h))
  coherence-htpy-eq-ap-precomp-Π refl = refl

  coherence-htpy-eq-ap-precomp-Π' :
    coherence-square-maps'
      ( ap (precomp-Π f C) {g} {h})
      ( htpy-eq)
      ( htpy-eq)
      ( precomp-Π f (eq-value g h))
  coherence-htpy-eq-ap-precomp-Π' = inv-htpy coherence-htpy-eq-ap-precomp-Π

  coherence-eq-htpy-ap-precomp-Π :
    coherence-square-maps
      ( precomp-Π f (eq-value g h))
      ( eq-htpy)
      ( eq-htpy)
      ( ap (precomp-Π f C) {g} {h})
  coherence-eq-htpy-ap-precomp-Π =
    vertical-inv-equiv-coherence-square-maps
      ( ap (precomp-Π f C))
      ( equiv-funext)
      ( equiv-funext)
      ( precomp-Π f (eq-value g h))
      ( coherence-htpy-eq-ap-precomp-Π)

  coherence-eq-htpy-ap-precomp-Π' :
    coherence-square-maps'
      ( precomp-Π f (eq-value g h))
      ( eq-htpy)
      ( eq-htpy)
      ( ap (precomp-Π f C) {g} {h})
  coherence-eq-htpy-ap-precomp-Π' = inv-htpy coherence-eq-htpy-ap-precomp-Π
```

### Precomposing functions `Π B C` by `f : A → B` is `k+1`-truncated if and only if precomposing homotopies is `k`-truncated

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B}
  {C : B → UU l3}
  where abstract

  is-trunc-map-succ-precomp-Π :
    ((g h : (b : B) → C b) → is-trunc-map k (precomp-Π f (eq-value g h))) →
    is-trunc-map (succ-𝕋 k) (precomp-Π f C)
  is-trunc-map-succ-precomp-Π H =
    is-trunc-map-succ-is-trunc-map-ap k (precomp-Π f C)
      ( λ g h →
        is-trunc-map-top-is-trunc-map-bottom-is-equiv k
          ( ap (precomp-Π f C))
          ( htpy-eq)
          ( htpy-eq)
          ( precomp-Π f (eq-value g h))
          ( coherence-htpy-eq-ap-precomp-Π f)
          ( funext g h)
          ( funext (g ∘ f) (h ∘ f))
          ( H g h))

  is-trunc-map-precomp-Π-eq-value-is-trunc-map-succ-precomp-Π :
    is-trunc-map (succ-𝕋 k) (precomp-Π f C) →
    (g h : (b : B) → C b) → is-trunc-map k (precomp-Π f (eq-value g h))
  is-trunc-map-precomp-Π-eq-value-is-trunc-map-succ-precomp-Π H g h =
    is-trunc-map-top-is-trunc-map-bottom-is-equiv k
      ( precomp-Π f (eq-value g h))
      ( eq-htpy)
      ( eq-htpy)
      ( ap (precomp-Π f C))
      ( coherence-eq-htpy-ap-precomp-Π f)
      ( is-equiv-eq-htpy g h)
      ( is-equiv-eq-htpy (g ∘ f) (h ∘ f))
      ( is-trunc-map-ap-is-trunc-map-succ k (precomp-Π f C) H g h)
```

### The dependent precomposition map at a dependent pair type

Given a map `f : X → Y` and a family `B : (y : Y) → A y → 𝒰` we have a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                                     precomp-Π f (λ y → Σ (A y) (B y))
            ((y : Y) → Σ (A y) (B y)) -----------------------------> ((x : X) → Σ (A (f x)) (B (f x)))
                       |                                                          |
                     ~ |                                                          | ~
                       ∨                                                          ∨
  Σ (a : (y : Y) → A y) ((y : Y) → B y (a y)) --------> Σ (a : (x : X) → A (f x)) ((x : X) → B (f x) (a x)).
                       map-Σ (precomp-Π f A) (λ a → precomp-Π f (λ y → B y (a y)))
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {X : UU l1} {Y : UU l2} {A : Y → UU l3} {B : (y : Y) → A y → UU l4}
  {f : X → Y}
  where

  coherence-precomp-Π-Σ :
    coherence-square-maps
      ( precomp-Π f (λ y → Σ (A y) (B y)))
      ( map-distributive-Π-Σ)
      ( map-distributive-Π-Σ)
      ( map-Σ
        ( λ a → (x : X) → B (f x) (a x))
        ( precomp-Π f A)
        ( λ a → precomp-Π f (λ y → B y (a y))))
  coherence-precomp-Π-Σ = refl-htpy
```
