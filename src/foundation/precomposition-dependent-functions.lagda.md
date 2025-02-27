# Precomposition of dependent functions

```agda
module foundation.precomposition-dependent-functions where

open import foundation-core.precomposition-dependent-functions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
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
is-trunc-map-succ-precomp-Π :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B}
  {C : B → UU l3} →
  ((g h : (b : B) → C b) → is-trunc-map k (precomp-Π f (eq-value g h))) →
  is-trunc-map (succ-𝕋 k) (precomp-Π f C)
is-trunc-map-succ-precomp-Π {k = k} {f = f} {C = C} H =
  is-trunc-map-is-trunc-map-ap k (precomp-Π f C)
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
