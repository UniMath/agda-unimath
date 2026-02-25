# `K`-Equivalences, with respect to a subuniverse `K`

```agda
module orthogonal-factorization-systems.equivalences-at-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.subuniverses
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections

open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

Given a [subuniverse](foundation.subuniverses.md) `K`, a map `f : A → B` is said
to be a
{{#concept "`K`-equivalence" Disambiguation="map of types, with respect to a subuniverse" Agda=is-subuniverse-equiv}}
if it satisfies the
{{#concept "universal property" Disambiguation="subuniverse connected map of types"}}
of `K`-equivalences:

For every `K`-type `U`, the
[precomposition map](foundation-core.precomposition-functions.md)

```text
 - ∘ f : (B → U) → (A → U)
```

is an [equivalence](foundation-core.equivalences.md).

Equivalently, a map `f : A → B` is a `K`-equivalence if

1. For every `U` in `K` and every `u : A → U` has a
   [unique](foundation-core.contractible-types.md)
   [extension](orthogonal-factorization-systems.extensions-maps.md) along `f`.
   I.e., the type of maps `u' : B → U` such that the following triangle
   [commutes](foundation-core.commuting-triangles-of-maps.md)
   ```text
        A
        |  \
      f |    \ u
        |      \
        ∨   u'   ∨
        B ------> U
   ```
   is contractible.

## Definition

### The predicate on maps of being `K`-equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  is-subuniverse-equiv : UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subuniverse-equiv =
    (U : type-subuniverse K) → is-equiv (precomp f (pr1 U))

  is-prop-is-subuniverse-equiv : is-prop is-subuniverse-equiv
  is-prop-is-subuniverse-equiv =
    is-prop-Π (λ U → is-property-is-equiv (precomp f (pr1 U)))

  is-subuniverse-equiv-Prop : Prop (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subuniverse-equiv-Prop =
    ( is-subuniverse-equiv , is-prop-is-subuniverse-equiv)
```

### The type of `K`-equivalences

```agda
subuniverse-equiv :
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) →
  UU l3 → UU l4 → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
subuniverse-equiv K A B = Σ (A → B) (is-subuniverse-equiv K)

module _
  {l1 l2 l3 l4 : Level}
  (K : subuniverse l1 l2) {A : UU l3} {B : UU l4}
  (f : subuniverse-equiv K A B)
  where

  map-subuniverse-equiv : A → B
  map-subuniverse-equiv = pr1 f

  is-subuniverse-equiv-subuniverse-equiv :
    is-subuniverse-equiv K map-subuniverse-equiv
  is-subuniverse-equiv-subuniverse-equiv = pr2 f
```

### The extension condition for `K`-equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  is-subuniverse-equiv-extension-condition : UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subuniverse-equiv-extension-condition =
    (U : type-subuniverse K) (u : A → pr1 U) → is-contr (extension-map f u)

  is-prop-is-subuniverse-equiv-extension-condition :
    is-prop is-subuniverse-equiv-extension-condition
  is-prop-is-subuniverse-equiv-extension-condition =
    is-prop-Π (λ U → is-prop-Π (λ u → is-property-is-contr))

  is-subuniverse-equiv-extension-condition-Prop : Prop (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subuniverse-equiv-extension-condition-Prop =
    ( is-subuniverse-equiv-extension-condition ,
      is-prop-is-subuniverse-equiv-extension-condition)
```

## Properties

### A map is a `K`-equivalence if and only if it satisfies the extension condition

A map `f : A → B` is a `K`-equivalence if and only if, for every `U` in `K` and
every map `u : A → U`, there is a unique extension of `u` along `f`.

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  abstract
    is-subuniverse-equiv-is-subuniverse-equiv-extension-condition :
      is-subuniverse-equiv-extension-condition K f →
      is-subuniverse-equiv K f
    is-subuniverse-equiv-is-subuniverse-equiv-extension-condition H U =
      is-equiv-is-contr-map
        ( λ u →
          is-contr-equiv
            ( extension-map f u)
            ( compute-extension-fiber-precomp f u)
            ( H U u))

  abstract
    is-subuniverse-equiv-extension-condition-is-subuniverse-equiv :
      is-subuniverse-equiv K f →
      is-subuniverse-equiv-extension-condition K f
    is-subuniverse-equiv-extension-condition-is-subuniverse-equiv H U u =
      is-contr-equiv'
        ( fiber (precomp f (pr1 U)) u)
        ( compute-extension-fiber-precomp f u)
        ( is-contr-map-is-equiv (H U) u)
```

### Equivalences are `K`-equivalences for all `K`

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  is-subuniverse-equiv-is-equiv : is-equiv f → is-subuniverse-equiv K f
  is-subuniverse-equiv-is-equiv H U = is-equiv-precomp-is-equiv f H (pr1 U)
```

### The identity map is a `K`-equivalence for all `K`

```agda
is-subuniverse-equiv-id :
  {l1 l2 l3 : Level} (K : subuniverse l1 l2) {A : UU l3} →
  is-subuniverse-equiv K (id' A)
is-subuniverse-equiv-id K = is-subuniverse-equiv-is-equiv K id is-equiv-id
```

### The `K`-equivalences are closed under homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {f g : A → B}
  where

  is-subuniverse-equiv-htpy :
    f ~ g → is-subuniverse-equiv K g → is-subuniverse-equiv K f
  is-subuniverse-equiv-htpy H G U =
    is-equiv-htpy (precomp g (pr1 U)) (htpy-precomp H (pr1 U)) (G U)

  is-subuniverse-equiv-htpy' :
    f ~ g → is-subuniverse-equiv K f → is-subuniverse-equiv K g
  is-subuniverse-equiv-htpy' H G U =
    is-equiv-htpy' (precomp f (pr1 U)) (htpy-precomp H (pr1 U)) (G U)
```

### The `K`-equivalences are closed under composition

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {C : UU l5}
  where

  is-subuniverse-equiv-comp :
    (g : B → C) (f : A → B) →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K g →
    is-subuniverse-equiv K (g ∘ f)
  is-subuniverse-equiv-comp g f F G U =
    is-equiv-comp (precomp f (pr1 U)) (precomp g (pr1 U)) (G U) (F U)

  subuniverse-equiv-comp :
    subuniverse-equiv K B C →
    subuniverse-equiv K A B →
    subuniverse-equiv K A C
  pr1 (subuniverse-equiv-comp g f) =
    map-subuniverse-equiv K g ∘ map-subuniverse-equiv K f
  pr2 (subuniverse-equiv-comp g f) =
    is-subuniverse-equiv-comp
      ( map-subuniverse-equiv K g)
      ( map-subuniverse-equiv K f)
      ( is-subuniverse-equiv-subuniverse-equiv K f)
      ( is-subuniverse-equiv-subuniverse-equiv K g)
```

### The class of `K`-equivalences has the left and right cancellation property

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {C : UU l5}
  (g : B → C) (f : A → B) (GF : is-subuniverse-equiv K (g ∘ f))
  where

  is-subuniverse-equiv-left-factor :
    is-subuniverse-equiv K f → is-subuniverse-equiv K g
  is-subuniverse-equiv-left-factor F U =
    is-equiv-right-factor (precomp f (pr1 U)) (precomp g (pr1 U)) (F U) (GF U)

  is-subuniverse-equiv-right-factor :
    is-subuniverse-equiv K g → is-subuniverse-equiv K f
  is-subuniverse-equiv-right-factor G U =
    is-equiv-left-factor (precomp f (pr1 U)) (precomp g (pr1 U)) (GF U) (G U)
```

### The class of `K`-equivalences satisfies the 3-for-2 property

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {X : UU l5}
  (f : A → X) (g : B → X) (h : A → B) (p : f ~ g ∘ h)
  where

  is-subuniverse-equiv-top-map-triangle :
      is-subuniverse-equiv K g →
      is-subuniverse-equiv K f →
      is-subuniverse-equiv K h
  is-subuniverse-equiv-top-map-triangle G F =
    is-subuniverse-equiv-right-factor K g h
      ( is-subuniverse-equiv-htpy' K p F)
      ( G)

  is-subuniverse-equiv-right-map-triangle :
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K h →
    is-subuniverse-equiv K g
  is-subuniverse-equiv-right-map-triangle F =
    is-subuniverse-equiv-left-factor K g h (is-subuniverse-equiv-htpy' K p F)

  is-subuniverse-equiv-left-map-triangle :
    is-subuniverse-equiv K h →
    is-subuniverse-equiv K g →
    is-subuniverse-equiv K f
  is-subuniverse-equiv-left-map-triangle H G =
    is-subuniverse-equiv-htpy K p (is-subuniverse-equiv-comp K g h H G)
```

### Sections of `K`-equivalences are `K`-equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {f : A → B}
  where

  is-subuniverse-equiv-map-section :
    (s : section f) →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K (map-section f s)
  is-subuniverse-equiv-map-section (s , h) =
    is-subuniverse-equiv-right-factor K f s
      ( is-subuniverse-equiv-is-equiv K (f ∘ s) (is-equiv-htpy-id h))
```

### Retractions of `K`-equivalences are `K`-equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {f : A → B}
  where

  is-subuniverse-equiv-map-retraction :
    (r : retraction f) →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K (map-retraction f r)
  is-subuniverse-equiv-map-retraction (r , h) =
    is-subuniverse-equiv-left-factor K r f
      ( is-subuniverse-equiv-is-equiv K (r ∘ f) (is-equiv-htpy-id h))
```

### Composing `K`-equivalences with equivalences

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {C : UU l5}
  where

  is-subuniverse-equiv-is-equiv-is-subuniverse-equiv :
    (g : B → C) (f : A → B) →
    is-subuniverse-equiv K g →
    is-equiv f →
    is-subuniverse-equiv K (g ∘ f)
  is-subuniverse-equiv-is-equiv-is-subuniverse-equiv g f eg ef =
    is-subuniverse-equiv-comp K g f
      ( is-subuniverse-equiv-is-equiv K f ef)
      ( eg)

  is-subuniverse-equiv-is-subuniverse-equiv-is-equiv :
    (g : B → C) (f : A → B) →
    is-equiv g →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K (g ∘ f)
  is-subuniverse-equiv-is-subuniverse-equiv-is-equiv g f eg ef =
    is-subuniverse-equiv-comp K g f
      ( ef)
      ( is-subuniverse-equiv-is-equiv K g eg)

  is-subuniverse-equiv-equiv-is-subuniverse-equiv :
    (g : B → C) (f : A ≃ B) →
    is-subuniverse-equiv K g →
    is-subuniverse-equiv K (g ∘ map-equiv f)
  is-subuniverse-equiv-equiv-is-subuniverse-equiv g (f , ef) eg =
    is-subuniverse-equiv-is-equiv-is-subuniverse-equiv g f eg ef

  is-subuniverse-equiv-is-subuniverse-equiv-equiv :
    (g : B ≃ C) (f : A → B) →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K (map-equiv g ∘ f)
  is-subuniverse-equiv-is-subuniverse-equiv-equiv (g , eg) f ef =
    is-subuniverse-equiv-is-subuniverse-equiv-is-equiv g f eg ef
```

## References

- The notion of `K`-equivalence is a generalization of the notion of
  `L`-equivalence, where `L` is a reflective subuniverse. These were studied in
  {{#cite CORS20}}.

{{#bibliography}}
