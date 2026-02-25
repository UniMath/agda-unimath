# Types colocal at maps

```agda
module orthogonal-factorization-systems.types-colocal-at-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-dependent-functions
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.retracts-of-arrows
open import foundation.retracts-of-types
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences-arrows
open import foundation-core.fibers-of-maps
```

</details>

## Idea

A type `A` is said to be
{{#concept "colocal" Disambiguation="type at a map" Agda=is-colocal}} at the map
`f : X → Y`, or **`f`-colocal**, if the
[postcomposition map](foundation-core.postcomposition-functions.md)

```text
  f ∘ - : (A → X) → (A → Y)
```

is an [equivalence](foundation-core.equivalences.md).

Equivalently, `A` is colocal if

1. the type of [sections](foundation-core.sections.md) `(x : A) → fiber f (h x)`
   is [contractible](foundation-core.contractible-types.md) for all `h : A → Y`.
2. The initial map `empty → A` is
   [left orthogonal](orthogonal-factorization-systems.orthogonal-maps.md) to
   `f`.

The notion of `f`-colocal types is dual to
[`f`-local types](orthogonal-factorization-systems.types-local-at-maps.md),
which is a type such that the
[precomposition map](foundation-core.precomposition-functions.md)

```text
  - ∘ f : (Y → A) → (X → A)
```

is an equivalence.

## Definitions

### Types colocal at dependent maps

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) {X : A → UU l2} {Y : A → UU l3}
  (f : {a : A} → X a → Y a)
  where

  is-dependent-map-colocal : UU (l1 ⊔ l2 ⊔ l3)
  is-dependent-map-colocal = is-equiv (postcomp-Π A (λ {a} → f {a}))

  is-property-is-dependent-map-colocal : is-prop is-dependent-map-colocal
  is-property-is-dependent-map-colocal = is-property-is-equiv (postcomp-Π A f)

  is-dependent-map-colocal-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  is-dependent-map-colocal-Prop = is-equiv-Prop (postcomp-Π A (λ {a} → f {a}))
```

### Types colocal at maps

```agda
module _
  {l1 l2 l3 : Level} {X : UU l2} {Y : UU l3}
  (f : X → Y) (A : UU l1)
  where

  is-colocal : UU (l1 ⊔ l2 ⊔ l3)
  is-colocal = is-dependent-map-colocal A f

  is-property-is-colocal : is-prop is-colocal
  is-property-is-colocal = is-property-is-dependent-map-colocal A f

  is-colocal-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  is-colocal-Prop = is-dependent-map-colocal-Prop A f
```

## Properties

### The fiber condition for `f`-colocal types

```agda
module _
  {l1 l2 l3 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3}
  (f : X → Y)
  where

  is-colocal-fiber-condition-is-colocal :
    is-colocal f A →
    ((h : A → Y) → is-contr ((x : A) → fiber f (h x)))
  is-colocal-fiber-condition-is-colocal H h =
    is-contr-equiv'
      ( fiber (postcomp A f) h)
      ( inv-compute-Π-fiber-postcomp A f h)
      ( is-contr-map-is-equiv H h)

  is-colocal-is-colocal-fiber-condition :
    ((h : A → Y) → is-contr ((x : A) → fiber f (h x))) →
    is-colocal f A
  is-colocal-is-colocal-fiber-condition H =
    is-equiv-is-contr-map
      ( λ h →
        is-contr-equiv
          ( (x : A) → fiber f (h x))
          ( inv-compute-Π-fiber-postcomp A f h)
          ( H h))

  is-colocal-is-colocal-fiber-condition' :
    ((h : A → Y) (x : A) → is-contr (fiber f (h x))) →
    is-colocal f A
  is-colocal-is-colocal-fiber-condition' H =
    is-colocal-is-colocal-fiber-condition (is-contr-Π ∘ H)
```

### `f`-colocal types are closed under equivalences

```agda
module _
  {l1 l2 l3 l4 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4}
  (f : X → Y)
  where

  is-colocal-equiv : A ≃ B → is-colocal f B → is-colocal f A
  is-colocal-equiv e is-colocal-B =
    is-equiv-htpy-equiv
      ( ( equiv-precomp e Y) ∘e
        ( postcomp B f , is-colocal-B) ∘e
        ( equiv-precomp (inv-equiv e) X))
      ( λ g → eq-htpy ((f ∘ g) ·l inv-htpy (is-retraction-map-inv-equiv e)))

  is-colocal-inv-equiv : B ≃ A → is-colocal f B → is-colocal f A
  is-colocal-inv-equiv e = is-colocal-equiv (inv-equiv e)
```

### Colocality is preserved by homotopies

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {A : UU l3} {f f' : X → Y}
  where

  is-colocal-htpy : (H : f ~ f') → is-colocal f' A → is-colocal f A
  is-colocal-htpy H = is-equiv-htpy (postcomp A f') (htpy-postcomp A H)

  is-colocal-inv-htpy : (H : f ~ f') → is-colocal f A → is-colocal f' A
  is-colocal-inv-htpy H = is-equiv-htpy' (postcomp A f) (htpy-postcomp A H)
```

### If `S` is `f`-colocal then `S` is colocal at every retract of `f`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : g retract-of-arrow f) (S : UU l5)
  where

  is-colocal-retract-arrow-is-colocal : is-colocal f S → is-colocal g S
  is-colocal-retract-arrow-is-colocal =
    is-equiv-retract-arrow-is-equiv
      ( postcomp S g)
      ( postcomp S f)
      ( retract-arrow-postcomp-retract-arrow g f R S)
```

In fact, the higher coherence of the retract is not needed:

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R₀ : X retract-of A) (R₁ : Y retract-of B)
  (i : coherence-square-maps' (inclusion-retract R₀) g f (inclusion-retract R₁))
  (r :
    coherence-square-maps'
      ( map-retraction-retract R₀)
      ( f)
      ( g)
      ( map-retraction-retract R₁))
  (S : UU l5)
  where

  is-colocal-retract-arrow-is-colocal' : is-colocal f S → is-colocal g S
  is-colocal-retract-arrow-is-colocal' =
    is-equiv-retract-arrow-is-equiv'
      ( postcomp S g)
      ( postcomp S f)
      ( retract-postcomp S R₀)
      ( retract-postcomp S R₁)
      ( inv-htpy
        ( postcomp-coherence-square-maps
          ( g)
          ( inclusion-retract R₀)
          ( inclusion-retract R₁)
          ( f)
          ( S)
          ( i)))
      ( inv-htpy
        ( postcomp-coherence-square-maps
          ( f)
          ( map-retraction-retract R₀)
          ( map-retraction-retract R₁)
          ( g)
          ( S)
          ( r)))
```

### If every type is `f`-colocal, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-equiv-is-colocal : ({l : Level} (A : UU l) → is-colocal f A) → is-equiv f
  is-equiv-is-colocal = is-equiv-is-equiv-postcomp f
```

### All types are colocal at equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-colocal-is-equiv :
    is-equiv f → {l : Level} (A : UU l) → is-colocal f A
  is-colocal-is-equiv = is-equiv-postcomp-is-equiv f
```

### A contractible type is `f`-colocal if and only if `f` is an equivalence

**Proof.** We have a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
  X ----> (A → X)
  |          |
  |          |
  ∨          ∨
  Y ----> (A → Y)
```

If `A` is contractible, then the top and bottom map are equivalences so the left
map is an equivalence if and only if the right map is.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  (A : UU l3) (is-contr-A : is-contr A)
  where

  is-equiv-is-colocal-is-contr : is-colocal f A → is-equiv f
  is-equiv-is-colocal-is-contr =
    is-equiv-source-is-equiv-target-equiv-arrow
      ( f)
      ( postcomp A f)
      ( equiv-diagonal-exponential-is-contr X is-contr-A ,
        equiv-diagonal-exponential-is-contr Y is-contr-A ,
        refl-htpy)

  is-colocal-is-equiv-is-contr : is-equiv f → is-colocal f A
  is-colocal-is-equiv-is-contr =
    is-equiv-target-is-equiv-source-equiv-arrow
      ( f)
      ( postcomp A f)
      ( equiv-diagonal-exponential-is-contr X is-contr-A ,
        equiv-diagonal-exponential-is-contr Y is-contr-A ,
        refl-htpy)
```

### A type `A` that is colocal at the initial map `empty → A` or `empty → unit` is empty

```agda
module _
  {l : Level} (A : UU l)
  where

  is-empty-is-colocal-initial-map :
    is-colocal (initial-map A) A → is-empty A
  is-empty-is-colocal-initial-map H = map-inv-is-equiv H id

  is-empty-is-colocal-map-unit-empty :
    is-colocal (initial-map unit) A → is-empty A
  is-empty-is-colocal-map-unit-empty H = map-inv-is-equiv H (terminal-map A)
```
