# Types colocal at maps

```agda
module orthogonal-factorization-systems.colocal-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-dependent-functions
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.retracts-of-maps
open import foundation.universal-property-equivalences
open import foundation.universe-levels
```

</details>

## Idea

A type `A` is said to be
{{#concept "colocal" Disambiguation="type at a map" Agda=is-colocal}} at the map
`f : Y → X`, or **`f`-colocal**, if the
[postcomposition map](foundation-core.postcomposition-functions.md)

```text
  f ∘_ : (A → Y) → (A → X)
```

is an [equivalence](foundation-core.equivalences.md). This is dual to the notion
of an [`f`-local type](orthogonal-factorization-systems.local-types.md), which
is a type such that the
[precomposition map](foundation-core.precompositon-functions.md)

```text
  _∘ f : (X → A) → (Y → A)
```

is an equivalence.

## Definition

### Types colocal at dependent maps

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) {Y : A → UU l2} {X : A → UU l3}
  (f : {a : A} → Y a → X a)
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
  {l1 l2 l3 : Level} {Y : UU l2} {X : UU l3}
  (f : Y → X) (A : UU l1)
  where

  is-colocal : UU (l1 ⊔ l2 ⊔ l3)
  is-colocal = is-dependent-map-colocal A f

  is-property-is-colocal : is-prop is-colocal
  is-property-is-colocal = is-property-is-dependent-map-colocal A f

  is-colocal-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  is-colocal-Prop = is-dependent-map-colocal-Prop A f
```

## Properties

### Colocal types are closed under equivalences

```agda
module _
  {l1 l2 l3 l4 : Level}
  {Y : UU l1} {X : UU l2} {A : X → UU l3} {B : X → UU l4}
  (f : Y → X)
  where

module _
  {l1 l2 l3 l4 : Level}
  {Y : UU l1} {X : UU l2} {A : UU l3} {B : UU l4}
  (f : Y → X)
  where

  is-colocal-equiv : A ≃ B → is-colocal f B → is-colocal f A
  is-colocal-equiv e is-colocal-B =
    is-equiv-htpy-equiv
      ( ( equiv-precomp e X) ∘e
        ( postcomp B f , is-colocal-B) ∘e
        ( equiv-precomp (inv-equiv e) Y))
      ( λ g →
        eq-htpy (λ x → ap (f ∘ g) (inv (is-retraction-map-inv-equiv e x))))

  is-colocal-inv-equiv : B ≃ A → is-colocal f B → is-colocal f A
  is-colocal-inv-equiv e = is-colocal-equiv (inv-equiv e)
```

### Colocality is preserved by homotopies

```agda
module _
  {l1 l2 l3 : Level} {Y : UU l1} {X : UU l2} {A : UU l3} {f f' : Y → X}
  where

  is-colocal-htpy : (H : f ~ f') → is-colocal f' A → is-colocal f A
  is-colocal-htpy H = is-equiv-htpy (postcomp A f') (htpy-postcomp A H)

  is-colocal-htpy' : (H : f ~ f') → is-colocal f A → is-colocal f' A
  is-colocal-htpy' H = is-equiv-htpy' (postcomp A f) (htpy-postcomp A H)
```

### If `S` is `f`-colocal then `S` is colocal at every retract of `f`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-map g) (S : UU l5)
  where

  is-colocal-retract-map-is-colocal : is-colocal g S → is-colocal f S
  is-colocal-retract-map-is-colocal =
    is-equiv-retract-map-is-equiv
      ( postcomp S f)
      ( postcomp S g)
      ( retract-map-postcomp-retract-map f g R S)
```

In fact, the higher coherence of the retract is not needed:

```text
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R₀ : A retract-of X) (R₁ : B retract-of Y)
  (i : coherence-square-maps' (inclusion-retract R₀) f g (inclusion-retract R₁))
  (r :
    coherence-square-maps'
      ( map-retraction-retract R₀)
      ( g)
      ( f)
      ( map-retraction-retract R₁))
  (S : UU l5)
  where

  is-colocal-retract-map-is-colocal' : is-colocal S g → is-colocal S f
  is-colocal-retract-map-is-colocal' =
    is-equiv-retract-map-is-equiv'
      ( postcomp S f)
      ( postcomp S g)
      ( retract-postcomp S R₁)
      ( retract-postcomp S R₀)
      ( postcomp-coherence-square-maps
        ( g)
        ( map-retraction-retract R₀)
        ( map-retraction-retract R₁)
        ( f)
        ( r)
        ( S))
      ( postcomp-coherence-square-maps
        ( f)
        ( inclusion-retract R₀)
        ( inclusion-retract R₁)
        ( g)
        ( i)
        ( S))
```

### If every type is `f`-colocal, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-equiv-is-colocal : ({l : Level} (A : UU l) → is-colocal f A) → is-equiv f
  is-equiv-is-colocal = is-equiv-is-equiv-postcomp f
```

### All types are colocal at equivalences

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-colocal-is-equiv :
    is-equiv f → {l : Level} (A : UU l) → is-colocal f A
  is-colocal-is-equiv is-equiv-f = is-equiv-postcomp-is-equiv f is-equiv-f
```

### A contractible type is `f`-colocal if and only if `f` is an equivalence

This remains to be formalized.

### A type that is colocal at the unique map `empty → unit` is empty

This remains to be formalized.

## See also

- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
