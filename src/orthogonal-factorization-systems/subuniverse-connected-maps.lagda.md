# Connected maps with respect to a subuniverse

```agda
module orthogonal-factorization-systems.subuniverse-connected-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.diagonal-maps-of-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.inhabited-types
open import foundation.iterated-successors-truncation-levels
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.precomposition-type-families
open import foundation.propositional-truncations
open import foundation.sections
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subuniverses
open import foundation.surjective-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.postcomposition-dependent-functions
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-maps

open import orthogonal-factorization-systems.localizations-at-subuniverses
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.relative-separations-types-subuniverses
open import orthogonal-factorization-systems.subuniverse-equivalences

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a [subuniverse](foundation.subuniverses.md) `K`, A map `f : A → B` is said
to be
{{#concept "`K`-connected" Disambiguation="map of types" Agda=is-subuniverse-connected-map}}
if it satisfies the
{{#concept "universal property" Disambiguation="subuniverse connected map of types"}}
of `K`-connected maps:

For every `K`-valued family `U` over `B`, the
[dependent precomposition map](foundation-core.precomposition-dependent-functions.md)

```text
 - ∘ f : ((b : B) → U b) → ((a : A) → U (f a))
```

is an [equivalence](foundation-core.equivalences.md).

Equivalently, a `K`-connected map `f : A → B` is a map that is
[left orthogonal](orthogonal-factorization-systems.orthogonal-maps.md) to maps
`h : C → B` whose fibers are in `K`.

## Definitions

### The predicate on maps of being `K`-connected

```agda
is-subuniverse-connected-map-Prop :
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2} →
  (A → B) → Prop (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
is-subuniverse-connected-map-Prop K {B = B} f =
  Π-Prop (B → type-subuniverse K) λ U → is-equiv-Prop (precomp-Π f (pr1 ∘ U))

is-subuniverse-connected-map :
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2} →
  (A → B) → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
is-subuniverse-connected-map K {B = B} f =
  (U : B → type-subuniverse K) → is-equiv (precomp-Π f (pr1 ∘ U))

is-prop-is-subuniverse-connected-map :
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4)
  {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-subuniverse-connected-map K f)
is-prop-is-subuniverse-connected-map K f =
  is-prop-type-Prop (is-subuniverse-connected-map-Prop K f)
```

### The type of `K`-connected maps between two types

```agda
subuniverse-connected-map :
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) →
  UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
subuniverse-connected-map K A B =
  type-subtype (is-subuniverse-connected-map-Prop K {A} {B})

module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2}
  where

  map-subuniverse-connected-map : subuniverse-connected-map K A B → A → B
  map-subuniverse-connected-map =
    inclusion-subtype (is-subuniverse-connected-map-Prop K)

  is-subuniverse-connected-map-subuniverse-connected-map :
    (f : subuniverse-connected-map K A B) →
    is-subuniverse-connected-map K (map-subuniverse-connected-map f)
  is-subuniverse-connected-map-subuniverse-connected-map =
    is-in-subtype-inclusion-subtype (is-subuniverse-connected-map-Prop K)

  emb-inclusion-subuniverse-connected-map :
    subuniverse-connected-map K A B ↪ (A → B)
  emb-inclusion-subuniverse-connected-map =
    emb-subtype (is-subuniverse-connected-map-Prop K)
```

### The type of `K`-connected maps into a type

```agda
Subuniverse-Connected-Map :
  {l1 l3 l4 : Level} (l2 : Level) (K : subuniverse l3 l4) (A : UU l1) →
  UU (l1 ⊔ lsuc l3 ⊔ l4 ⊔ lsuc l2)
Subuniverse-Connected-Map l2 K A = Σ (UU l2) (subuniverse-connected-map K A)

module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4)
  {A : UU l1} (f : Subuniverse-Connected-Map l2 K A)
  where

  type-Subuniverse-Connected-Map : UU l2
  type-Subuniverse-Connected-Map = pr1 f

  subuniverse-connected-map-Subuniverse-Connected-Map :
    subuniverse-connected-map K A type-Subuniverse-Connected-Map
  subuniverse-connected-map-Subuniverse-Connected-Map = pr2 f

  map-Subuniverse-Connected-Map : A → type-Subuniverse-Connected-Map
  map-Subuniverse-Connected-Map =
    map-subuniverse-connected-map K
      ( subuniverse-connected-map-Subuniverse-Connected-Map)

  is-subuniverse-connected-map-Subuniverse-Connected-Map :
    is-subuniverse-connected-map K map-Subuniverse-Connected-Map
  is-subuniverse-connected-map-Subuniverse-Connected-Map =
    is-subuniverse-connected-map-subuniverse-connected-map K
      ( subuniverse-connected-map-Subuniverse-Connected-Map)
```

## Properties

### Equivalent characterizations of `K`-connected maps

#### Contractible fiber-localization condition

Given a subuniverse `K` then a map `f` is `K`-connected if if the fibers are
`K`-equivalent to contractible types.

**Proof.** We have an equivalence of arrows

```text
                               ~
    ((b : B) → unit → U b) --------> ((b : B) → U b)
               |                            |
               |                            | precomp-Π f U
               |                            |
               ∨               ~            ∨
  ((b : B) → fiber f b → U b) ---> ((a : A) → U (f a))
```

where the left-hand map is
`map-Π (λ b → precomp (terminal-map (fiber f b)) (U b))`, hence if each terminal
map is a `K`-equivalence then this is an equivalence as well. ∎

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-subuniverse-connected-map-is-subuniverse-equiv-terminal-map-fibers :
    ((b : B) → is-subuniverse-equiv K (terminal-map (fiber f b))) →
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-is-subuniverse-equiv-terminal-map-fibers H U =
    is-equiv-target-is-equiv-source-equiv-arrow
      ( map-Π (λ b → precomp (terminal-map (fiber f b)) (pr1 (U b))))
      ( precomp-Π f (pr1 ∘ U))
      ( ( equiv-Π-equiv-family
          ( λ b → equiv-universal-property-unit (pr1 (U b)))) ,
        ( equiv-universal-property-family-of-fibers f (pr1 ∘ U)) ,
        ( refl-htpy))
      ( is-equiv-map-Π-is-fiberwise-equiv (λ b → H b (U b)))
```

#### Constant map condition on fibers

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-subuniverse-connected-map-is-equiv-diagonal-exponential-fibers :
    ( (b : B) (U : type-subuniverse K) →
      is-equiv (diagonal-exponential (pr1 U) (fiber f b))) →
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-is-equiv-diagonal-exponential-fibers H =
    is-subuniverse-connected-map-is-subuniverse-equiv-terminal-map-fibers K f
      ( λ b U →
        is-equiv-precomp-terminal-map-is-equiv-diagonal-exponential (H b U))
```

#### Section condition

A map is `K`-connected if and only if its dependent precomposition maps admit
sections and the fibers have `K`-localizations.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (Kfib : B → UU l3) (η : (b : B) → fiber f b → Kfib b)
    ( is-htpy-injective-precomp-η-Kfib :
        (b : B) {g h : Kfib b → Kfib b} →
        precomp (η b) (Kfib b) g ~ precomp (η b) (Kfib b) h → g ~ h)
  where

  is-contr-subuniverse-localization-fiber-has-section-precomp-Π'' :
    ( fiber-Π-precomp-Π' f Kfib (λ a → η (f a) (a , refl))) →
    ((b : B) → is-contr (Kfib b))
  is-contr-subuniverse-localization-fiber-has-section-precomp-Π'' Fη b =
      ( pr1 (Fη b) ,
        is-htpy-injective-precomp-η-Kfib b
          ( λ where (a , refl) → pr2 (Fη b) (a , refl)))

  is-contr-subuniverse-localization-fiber-has-section-precomp-Π' :
    fiber (precomp-Π f Kfib) (λ a → η (f a) (a , refl)) →
    ((b : B) → is-contr (Kfib b))
  is-contr-subuniverse-localization-fiber-has-section-precomp-Π' (s , H) b =
    ( s b ,
      is-htpy-injective-precomp-η-Kfib b (λ where (a , refl) → htpy-eq H a))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  {l4 : Level} (K : subuniverse l3 l4)
  (Kfib : (b : B) → subuniverse-localization K (fiber f b))
  (s : (U : B → type-subuniverse K) → section (precomp-Π f (pr1 ∘ U)))
  where

  is-contr-subuniverse-localization-fiber-has-section-precomp-Π :
    ((b : B) → is-contr (pr1 (Kfib b)))
  is-contr-subuniverse-localization-fiber-has-section-precomp-Π =
    is-contr-subuniverse-localization-fiber-has-section-precomp-Π' f
      ( type-subuniverse-localization K ∘ Kfib)
      ( unit-subuniverse-localization K ∘ Kfib)
      ( λ b H →
        htpy-eq
          ( is-injective-is-equiv
            ( is-subuniverse-equiv-unit-subuniverse-localization K (Kfib b)
              ( type-subuniverse-subuniverse-localization K (Kfib b)))
            ( eq-htpy H)))
      ( is-split-surjective-section
        ( precomp-Π f (type-subuniverse-localization K ∘ Kfib))
        ( s (type-subuniverse-subuniverse-localization K ∘ Kfib))
        ( λ a → unit-subuniverse-localization K (Kfib (f a)) (a , refl)))

  is-subuniverse-equiv-terminal-map-fibers-has-section-precomp-Π :
    (b : B) → is-subuniverse-equiv K (terminal-map (fiber f b))
  is-subuniverse-equiv-terminal-map-fibers-has-section-precomp-Π b =
    is-subuniverse-equiv-comp K
      ( terminal-map (type-subuniverse-localization K (Kfib b)))
      ( unit-subuniverse-localization K (Kfib b))
      ( is-subuniverse-equiv-unit-subuniverse-localization K (Kfib b))
      ( is-subuniverse-equiv-is-equiv K
        ( terminal-map (type-subuniverse-localization K (Kfib b)))
        ( is-equiv-terminal-map-is-contr
          ( is-contr-subuniverse-localization-fiber-has-section-precomp-Π b)))

  is-subuniverse-connected-map-has-section-precomp-Π :
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-has-section-precomp-Π =
    is-subuniverse-connected-map-is-subuniverse-equiv-terminal-map-fibers K f
      ( is-subuniverse-equiv-terminal-map-fibers-has-section-precomp-Π)
```

#### Surjection condition

A map is `K`-connected if and only if its dependent precomposition maps are
surjective and the fibers have `K`-localizations.

In fact, it suffices that the fibers have `K`-localizations and the family

```text
  b ↦
    Σ ( u : K(fiber f b)),
      ( ((a , p) : fiber f b) →
        dependent-identification (b ↦ K(fiber f b)) p u (η (f a) (a , refl)))
```

is inhabited, which is a slightly weaker condition than inhabitedness of the
fiber of `precomp-Π f` over the map `a ↦ η (f a) (a , refl)`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (Kfib : B → UU l3)
  (η : (b : B) → fiber f b → Kfib b)
  ( is-htpy-injective-precomp-η-Kfib :
      (b : B) {g h : Kfib b → Kfib b} →
      precomp (η b) (Kfib b) g ~ precomp (η b) (Kfib b) h → g ~ h)
  where

  abstract
    is-contr-subuniverse-localization-fiber-is-inhabited-family-fiber-Π-precomp-Π' :
      ( (b : B) →
        is-inhabited
          ( family-fiber-Π-precomp-Π' f Kfib (λ a → η (f a) (a , refl)) b)) →
      ((b : B) → is-contr (Kfib b))
    is-contr-subuniverse-localization-fiber-is-inhabited-family-fiber-Π-precomp-Π'
      Fη b =
      rec-trunc-Prop
        ( is-contr-Prop (Kfib b))
        ( λ (sb , Hb) →
          ( sb ,
            is-htpy-injective-precomp-η-Kfib b
              ( λ where (a , refl) → Hb (a , refl))))
        ( Fη b)

  is-contr-subuniverse-localization-fiber-is-inhabited-fiber-precomp-Π :
    is-inhabited (fiber (precomp-Π f Kfib) (λ a → η (f a) (a , refl))) →
    ((b : B) → is-contr (Kfib b))
  is-contr-subuniverse-localization-fiber-is-inhabited-fiber-precomp-Π
    s b =
    rec-trunc-Prop
      ( is-contr-Prop (Kfib b))
      ( λ s →
        is-contr-subuniverse-localization-fiber-has-section-precomp-Π'
          f Kfib η is-htpy-injective-precomp-η-Kfib s b)
      ( s)

module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4)
  {A : UU l1} {B : UU l2} (f : A → B)
  (Kfib : (b : B) → subuniverse-localization K (fiber f b))
  where

  is-contr-subuniverse-localization-fiber-is-inhabited-family-fiber-Π-precomp-Π :
    ( (b : B) →
      is-inhabited
        ( family-fiber-Π-precomp-Π' f
          ( type-subuniverse-localization K ∘ Kfib)
          ( λ a → unit-subuniverse-localization K (Kfib (f a)) (a , refl))
          ( b))) →
    ((b : B) → is-contr (type-subuniverse-localization K (Kfib b)))
  is-contr-subuniverse-localization-fiber-is-inhabited-family-fiber-Π-precomp-Π =
    is-contr-subuniverse-localization-fiber-is-inhabited-family-fiber-Π-precomp-Π'
      ( f)
      ( type-subuniverse-localization K ∘ Kfib)
      ( unit-subuniverse-localization K ∘ Kfib)
      ( λ b H →
        htpy-eq
          ( is-injective-is-equiv
            ( is-subuniverse-equiv-unit-subuniverse-localization K (Kfib b)
              ( type-subuniverse-subuniverse-localization K (Kfib b)))
            ( eq-htpy H)))

  is-contr-subuniverse-localization-fiber-is-surjective-precomp-Π :
    ((U : B → type-subuniverse K) → is-surjective (precomp-Π f (pr1 ∘ U))) →
    ((b : B) → is-contr (pr1 (Kfib b)))
  is-contr-subuniverse-localization-fiber-is-surjective-precomp-Π s =
    is-contr-subuniverse-localization-fiber-is-inhabited-fiber-precomp-Π f
      ( type-subuniverse-localization K ∘ Kfib)
      ( unit-subuniverse-localization K ∘ Kfib)
      ( λ b H →
        htpy-eq
          ( is-injective-is-equiv
            ( is-subuniverse-equiv-unit-subuniverse-localization K (Kfib b)
              ( type-subuniverse-subuniverse-localization K (Kfib b)))
            ( eq-htpy H)))
      ( s ( type-subuniverse-subuniverse-localization K ∘ Kfib)
          ( λ a → unit-subuniverse-localization K (Kfib (f a)) (a , refl)))

  is-subuniverse-equiv-terminal-map-fibers-is-inhabited-family-fiber-Π-precomp-Π :
    ( (b : B) →
      is-inhabited
        ( family-fiber-Π-precomp-Π' f
          ( type-subuniverse-localization K ∘ Kfib)
          ( λ a → unit-subuniverse-localization K (Kfib (f a)) (a , refl))
          ( b)))  →
    (b : B) → is-subuniverse-equiv K (terminal-map (fiber f b))
  is-subuniverse-equiv-terminal-map-fibers-is-inhabited-family-fiber-Π-precomp-Π
    s b =
    is-subuniverse-equiv-comp K
      ( terminal-map (type-subuniverse-localization K (Kfib b)))
      ( unit-subuniverse-localization K (Kfib b))
      ( is-subuniverse-equiv-unit-subuniverse-localization K (Kfib b))
      ( is-subuniverse-equiv-is-equiv K
        ( terminal-map (type-subuniverse-localization K (Kfib b)))
        ( is-equiv-terminal-map-is-contr
          ( is-contr-subuniverse-localization-fiber-is-inhabited-family-fiber-Π-precomp-Π
            s b)))

  is-subuniverse-connected-map-is-inhabited-family-fiber-Π-precomp-Π :
    ( (b : B) →
      is-inhabited
        ( family-fiber-Π-precomp-Π' f
          ( type-subuniverse-localization K ∘ Kfib)
          ( λ a → unit-subuniverse-localization K (Kfib (f a)) (a , refl))
          ( b))) →
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-is-inhabited-family-fiber-Π-precomp-Π Fη =
    is-subuniverse-connected-map-is-subuniverse-equiv-terminal-map-fibers K f
      ( is-subuniverse-equiv-terminal-map-fibers-is-inhabited-family-fiber-Π-precomp-Π
        ( Fη))
```

### Characterizing equality of `K`-connected maps

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2}
  where

  htpy-subuniverse-connected-map :
    (f g : subuniverse-connected-map K A B) → UU (l1 ⊔ l2)
  htpy-subuniverse-connected-map f g =
    map-subuniverse-connected-map K f ~ map-subuniverse-connected-map K g

  refl-htpy-subuniverse-connected-map :
    (f : subuniverse-connected-map K A B) → htpy-subuniverse-connected-map f f
  refl-htpy-subuniverse-connected-map f = refl-htpy

  is-torsorial-htpy-subuniverse-connected-map :
    (f : subuniverse-connected-map K A B) →
    is-torsorial (htpy-subuniverse-connected-map f)
  is-torsorial-htpy-subuniverse-connected-map f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-subuniverse-connected-map K f))
      ( is-prop-is-subuniverse-connected-map K)
      ( map-subuniverse-connected-map K f)
      ( refl-htpy-subuniverse-connected-map f)
      ( is-subuniverse-connected-map-subuniverse-connected-map K f)

  htpy-eq-connected-map :
    (f g : subuniverse-connected-map K A B) →
    f ＝ g → htpy-subuniverse-connected-map f g
  htpy-eq-connected-map f .f refl = refl-htpy-subuniverse-connected-map f

  is-equiv-htpy-eq-connected-map :
    (f g : subuniverse-connected-map K A B) →
    is-equiv (htpy-eq-connected-map f g)
  is-equiv-htpy-eq-connected-map f =
    fundamental-theorem-id
      ( is-torsorial-htpy-subuniverse-connected-map f)
      ( htpy-eq-connected-map f)

  extensionality-connected-map :
    (f g : subuniverse-connected-map K A B) →
    (f ＝ g) ≃ htpy-subuniverse-connected-map f g
  pr1 (extensionality-connected-map f g) = htpy-eq-connected-map f g
  pr2 (extensionality-connected-map f g) = is-equiv-htpy-eq-connected-map f g

  eq-htpy-subuniverse-connected-map :
    (f g : subuniverse-connected-map K A B) →
    htpy-subuniverse-connected-map f g → (f ＝ g)
  eq-htpy-subuniverse-connected-map f g =
    map-inv-equiv (extensionality-connected-map f g)
```

### All maps are `Contr`-connected

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-Contr-connected-map : is-subuniverse-connected-map (is-contr-Prop {l3}) f
  is-Contr-connected-map U =
    is-equiv-is-contr
      ( precomp-Π f (pr1 ∘ U))
      ( is-contr-Π (pr2 ∘ U))
      ( is-contr-Π (pr2 ∘ U ∘ f))
```

### Equivalences are `K`-connected for any `K`

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2}
  where

  is-subuniverse-connected-map-is-equiv :
    {f : A → B} → is-equiv f → is-subuniverse-connected-map K f
  is-subuniverse-connected-map-is-equiv H U =
    is-equiv-precomp-Π-is-equiv H (pr1 ∘ U)

  is-subuniverse-connected-map-equiv :
    (e : A ≃ B) → is-subuniverse-connected-map K (map-equiv e)
  is-subuniverse-connected-map-equiv e =
    is-subuniverse-connected-map-is-equiv (is-equiv-map-equiv e)

  subuniverse-connected-map-equiv :
    (A ≃ B) → subuniverse-connected-map K A B
  subuniverse-connected-map-equiv e =
    ( map-equiv e , is-subuniverse-connected-map-equiv e)
```

### `K`-connected maps are `K`-equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-subuniverse-equiv-is-subuniverse-connected-map :
    is-subuniverse-connected-map K f → is-subuniverse-equiv K f
  is-subuniverse-equiv-is-subuniverse-connected-map F U = F (λ _ → U)
```

### The composition of two `K`-connected maps is `K`-connected

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l4 l5)
  {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-subuniverse-connected-map-comp :
    {g : B → C} {f : A → B} →
    is-subuniverse-connected-map K g →
    is-subuniverse-connected-map K f →
    is-subuniverse-connected-map K (g ∘ f)
  is-subuniverse-connected-map-comp {g} {f} G F U =
    is-equiv-comp
      ( precomp-Π f (pr1 ∘ U ∘ g))
      ( precomp-Π g (pr1 ∘ U))
      ( G U)
      ( F (U ∘ g))

  comp-subuniverse-connected-map :
    subuniverse-connected-map K B C →
    subuniverse-connected-map K A B →
    subuniverse-connected-map K A C
  pr1 (comp-subuniverse-connected-map g f) =
    map-subuniverse-connected-map K g ∘ map-subuniverse-connected-map K f
  pr2 (comp-subuniverse-connected-map g f) =
    is-subuniverse-connected-map-comp
      ( is-subuniverse-connected-map-subuniverse-connected-map K g)
      ( is-subuniverse-connected-map-subuniverse-connected-map K f)
```

### Right cancellation of `K`-connected maps

```agda
is-subuniverse-connected-map-left-factor :
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l4 l5)
  {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {h : A → B} →
  is-subuniverse-connected-map K h →
  is-subuniverse-connected-map K (g ∘ h) →
  is-subuniverse-connected-map K g
is-subuniverse-connected-map-left-factor K {g = g} {h} H GH U =
  is-equiv-right-factor
    ( precomp-Π h (pr1 ∘ U ∘ g))
    ( precomp-Π g (pr1 ∘ U))
    ( H (U ∘ g))
    ( GH U)
```

### Characterization of the identity type of `Subuniverse-Connected-Map l2 K A`

```agda
equiv-Subuniverse-Connected-Map :
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} →
  (f g : Subuniverse-Connected-Map l2 K A) → UU (l1 ⊔ l2)
equiv-Subuniverse-Connected-Map K f g =
  Σ ( type-Subuniverse-Connected-Map K f ≃ type-Subuniverse-Connected-Map K g)
    ( λ e →
      map-equiv e ∘ map-Subuniverse-Connected-Map K f ~
      map-Subuniverse-Connected-Map K g)

module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1}
  (f : Subuniverse-Connected-Map l2 K A)
  where

  id-equiv-Subuniverse-Connected-Map : equiv-Subuniverse-Connected-Map K f f
  id-equiv-Subuniverse-Connected-Map = (id-equiv , refl-htpy)

  is-torsorial-equiv-Subuniverse-Connected-Map :
    is-torsorial (equiv-Subuniverse-Connected-Map K f)
  is-torsorial-equiv-Subuniverse-Connected-Map =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Subuniverse-Connected-Map K f))
      ( type-Subuniverse-Connected-Map K f , id-equiv)
      ( is-torsorial-htpy-subuniverse-connected-map K
        ( subuniverse-connected-map-Subuniverse-Connected-Map K f))

  equiv-eq-Subuniverse-Connected-Map :
    (g : Subuniverse-Connected-Map l2 K A) →
    f ＝ g → equiv-Subuniverse-Connected-Map K f g
  equiv-eq-Subuniverse-Connected-Map .f refl =
    id-equiv-Subuniverse-Connected-Map

  is-equiv-equiv-eq-Subuniverse-Connected-Map :
    (g : Subuniverse-Connected-Map l2 K A) →
    is-equiv (equiv-eq-Subuniverse-Connected-Map g)
  is-equiv-equiv-eq-Subuniverse-Connected-Map =
    fundamental-theorem-id
      ( is-torsorial-equiv-Subuniverse-Connected-Map)
      ( equiv-eq-Subuniverse-Connected-Map)

  extensionality-Subuniverse-Connected-Map :
    (g : Subuniverse-Connected-Map l2 K A) →
    (f ＝ g) ≃ equiv-Subuniverse-Connected-Map K f g
  extensionality-Subuniverse-Connected-Map g =
    ( equiv-eq-Subuniverse-Connected-Map g ,
      is-equiv-equiv-eq-Subuniverse-Connected-Map g)

  eq-equiv-Subuniverse-Connected-Map :
    (g : Subuniverse-Connected-Map l2 K A) →
    equiv-Subuniverse-Connected-Map K f g → f ＝ g
  eq-equiv-Subuniverse-Connected-Map g =
    map-inv-equiv (extensionality-Subuniverse-Connected-Map g)
```

### `K`-connected maps are closed under cobase change

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (K : subuniverse l5 l6)
  {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  where

  is-subuniverse-connected-map-cobase-change' :
    dependent-pullback-property-pushout f g c →
    is-subuniverse-connected-map K g →
    is-subuniverse-connected-map K (horizontal-map-cocone f g c)
  is-subuniverse-connected-map-cobase-change' H G U =
    is-equiv-vertical-map-is-pullback _ _
      ( cone-dependent-pullback-property-pushout f g c (pr1 ∘ U))
      ( G (U ∘ vertical-map-cocone f g c))
      ( H (pr1 ∘ U))

  is-subuniverse-connected-map-cobase-change :
    is-pushout f g c →
    is-subuniverse-connected-map K g →
    is-subuniverse-connected-map K (horizontal-map-cocone f g c)
  is-subuniverse-connected-map-cobase-change H =
    is-subuniverse-connected-map-cobase-change'
      ( dependent-pullback-property-pushout-is-pushout f g c H)
```

### `K`-connected maps are closed under retracts of maps

**Proof.** Given a retract of maps

```text
          i         r
    A' ------> A ------> A'
    |          |         |
  f'|     I    f    R    | f'
    ∨          ∨         ∨
    B' ------> B ------> B'
          i'        r'
```

with higher coherence `α`, and a `K`-valued family `U` over `B'` there is by
functoriality an induced retract of dependent precomposition maps

```text
     Π(A'),(U∘f') <--- Π(A'),(U∘r'∘i'∘f) <--- Π(A),(U∘r'∘f) <--- Π(A'),(U∘f')
          ∧                                         ∧                 ∧
          |            α* □ Π(I),(U∘r')             |      Π(R),U     |
  Π(f'),U |                                    Π(f),(U∘r')            | Π(f'),U
          |                                         |                 |
     Π(B'),U <--------- Π(B'),(U∘r'∘i') <----- Π(B),(U∘r') <--- Π(B'),(U),
```

and since equivalences are closed under retracts of maps, if `f` is
`K`-connected then so is `f'`. ∎

Note that, since equivalences are already closed under noncoherent retracts of
maps, we are not obligated to produce the higher coherence of this retract.

> This remains to be formalized.

### The total map induced by a family of maps is `K`-connected if and only if all maps in the family are `K`-connected

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l4 l5)
  {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  is-subuniverse-connected-map-tot-is-fiberwise-subuniverse-connected-map :
    ((x : A) → is-subuniverse-connected-map K (f x)) →
    is-subuniverse-connected-map K (tot f)
  is-subuniverse-connected-map-tot-is-fiberwise-subuniverse-connected-map H U =
    is-equiv-source-is-equiv-target-equiv-arrow
      ( precomp-Π (tot f) (pr1 ∘ U))
      ( map-Π (λ i → precomp-Π (f i) (pr1 ∘ U ∘ (i ,_))))
      ( equiv-ev-pair , equiv-ev-pair , refl-htpy)
      ( is-equiv-map-Π-is-fiberwise-equiv (λ i → H i (U ∘ (i ,_))))

  -- is-fiberwise-subuniverse-connected-map-is-subuniverse-connected-map-tot :
  --   is-subuniverse-connected-map K (tot f) →
  --   (x : A) → is-subuniverse-connected-map K (f x)
  -- is-fiberwise-subuniverse-connected-map-is-subuniverse-connected-map-tot H = {!   !}
  --   -- is-subuniverse-connected-equiv (inv-compute-fiber-tot f (x , y)) (H (x , y))
```

### Coproducts of `K`-connected maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (K : subuniverse l5 l6)
  {A : UU l1} {B : UU l2} {A' : UU l3} {B' : UU l4}
  {f : A → B} {f' : A' → B'}
  where

  is-subuniverse-connected-map-coproduct :
    is-subuniverse-connected-map K f →
    is-subuniverse-connected-map K f' →
    is-subuniverse-connected-map K (map-coproduct f f')
  is-subuniverse-connected-map-coproduct F F' U =
    is-equiv-source-is-equiv-target-equiv-arrow
      ( precomp-Π (map-coproduct f f') (pr1 ∘ U))
      ( map-product
        ( precomp-Π f (pr1 ∘ U ∘ inl))
        ( precomp-Π f' (pr1 ∘ U ∘ inr)))
      ( equiv-dependent-universal-property-coproduct
        ( pr1 ∘ U) ,
        equiv-dependent-universal-property-coproduct
          ( pr1 ∘ U ∘ map-coproduct f f') ,
        refl-htpy)
      ( is-equiv-map-product _ _ (F (U ∘ inl)) (F' (U ∘ inr)))
```

### The map on dependent pair types induced by a `K`-connected map is a `K`-equivalence

This requires the added assumption that `K` is closed under exponentiation by
arbitrary types.

This is a generalization of Lemma 2.27 in {{#cite CORS20}}, since the unit map
of the $ΣK$-localization is a $ΣK$-equivalence, and $ΣK$-equivalences are in
particular $K$-connected.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l3 l4)
  {A : UU l1} {B : UU l2} (f : subuniverse-connected-map K A B) (P : B → UU l3)
  where

  map-Σ-map-base-subuniverse-connected-map :
    Σ A (P ∘ map-subuniverse-connected-map K f) → Σ B P
  map-Σ-map-base-subuniverse-connected-map =
    map-Σ-map-base (map-subuniverse-connected-map K f) P

  is-subuniverse-equiv-map-Σ-map-base-subuniverse-connected-map :
    ((V : UU l3) (U : type-subuniverse K) → is-in-subuniverse K (V → pr1 U)) →
    is-subuniverse-equiv K map-Σ-map-base-subuniverse-connected-map
  is-subuniverse-equiv-map-Σ-map-base-subuniverse-connected-map H U =
    is-equiv-source-is-equiv-target-equiv-arrow
      ( precomp map-Σ-map-base-subuniverse-connected-map (pr1 U))
      ( precomp-Π (map-subuniverse-connected-map K f) (λ y → (b : P y) → pr1 U))
      ( equiv-ev-pair , equiv-ev-pair , refl-htpy)
      ( is-subuniverse-connected-map-subuniverse-connected-map K f
        ( λ y → ((P y → pr1 U) , H (P y) U)))
```

### There is a `K`-equivalence between the fiber of a map and the fiber of its `ΣK`-localization

This is generalization of Corollary 2.29 in {{#cite CORS20}}.

Assume given arbitrary `f : A → B` and `Σ(δ)K`-equivalences `A → A'` and
`B → B'`. Then there is

```text
  fiber f b = Σ A (λ a → f a = b)
            → Σ A (λ a → ║f a ＝ b║)
            ≃ Σ A (λ a → |f a| = |b|)
            ≃ Σ A (λ a → ║f║ |a| = |b|)
            → Σ ║A║ (λ t → ║f║ t = |b|)
            = fiber ║f║ |b|
```

where the first and last maps are `K`-equivalences.

```text
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4)
  {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  fiber-map-trunc-fiber :
    fiber f b → fiber (map-trunc (succ-𝕋 K) f) (unit-trunc b)
  fiber-map-trunc-fiber =
    ( map-Σ-map-base-subuniverse-equiv
      ( λ t → map-trunc (succ-𝕋 K) f t ＝ unit-trunc b)) ∘
    ( tot
      ( λ a →
        ( concat (naturality-unit-trunc (succ-𝕋 K) f a) (unit-trunc b)) ∘
        ( map-effectiveness-trunc K (f a) b) ∘
        ( unit-trunc)))

  abstract
    is-subuniverse-equiv-fiber-map-trunc-fiber :
      is-subuniverse-equiv K fiber-map-trunc-fiber
    is-subuniverse-equiv-fiber-map-trunc-fiber =
      is-subuniverse-equiv-comp
        ( map-Σ-map-base-subuniverse-equiv
          ( λ t → map-trunc (succ-𝕋 K) f t ＝ unit-trunc b))
        ( tot
          ( λ a →
            ( concat (naturality-unit-trunc (succ-𝕋 K) f a) (unit-trunc b)) ∘
            ( map-effectiveness-trunc K (f a) b) ∘
            ( unit-trunc)))
        ( is-subuniverse-equiv-is-subuniverse-equiv-equiv
          ( equiv-tot
            ( λ a →
              ( equiv-concat
                ( naturality-unit-trunc (succ-𝕋 K) f a)
                ( unit-trunc b)) ∘e
              ( effectiveness-trunc K (f a) b)))
          ( λ (a , p) → a , unit-trunc p)
          ( is-equiv-map-equiv (equiv-trunc-Σ K)))
        ( is-subuniverse-equiv-map-Σ-map-base-unit-trunc
          ( λ t → map-trunc (succ-𝕋 K) f t ＝ unit-trunc b))

  subuniverse-equiv-fiber-map-trunc-fiber :
    subuniverse-equiv K
      ( fiber f b)
      ( fiber (map-trunc (succ-𝕋 K) f) (unit-trunc b))
  pr1 subuniverse-equiv-fiber-map-trunc-fiber =
    fiber-map-trunc-fiber
  pr2 subuniverse-equiv-fiber-map-trunc-fiber =
    is-subuniverse-equiv-fiber-map-trunc-fiber

  equiv-trunc-fiber-map-trunc-fiber :
    type-trunc K (fiber f b) ≃
    type-trunc K (fiber (map-trunc (succ-𝕋 K) f) (unit-trunc b))
  equiv-trunc-fiber-map-trunc-fiber =
    equiv-trunc-subuniverse-equiv K
      ( subuniverse-equiv-fiber-map-trunc-fiber)
```
