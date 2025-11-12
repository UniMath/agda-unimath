# Connected maps with respect to a subuniverse

```agda
module orthogonal-factorization-systems.subuniverse-connected-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.inhabited-types
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositional-truncations
open import foundation.retracts-of-maps
open import foundation.sections
open import foundation.split-surjective-maps
open import foundation.subtype-identity-principle
open import foundation.subuniverses
open import foundation.surjective-maps
open import foundation.unit-type
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
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families

open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.localizations-at-subuniverses
open import orthogonal-factorization-systems.subuniverse-connected-types
open import orthogonal-factorization-systems.subuniverse-equivalences

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a [subuniverse](foundation.subuniverses.md) `K`, a map `f : A → B` is said
to be
{{#concept "`K`-connected" Disambiguation="map of types, with respect to a subuniverse" Agda=is-subuniverse-connected-map}}
if it satisfies the
{{#concept "universal property" Disambiguation="subuniverse connected map of types"}}
of `K`-connected maps:

For every `K`-valued family `U` over `B`, the
[dependent precomposition map](foundation-core.precomposition-dependent-functions.md)

```text
 - ∘ f : ((b : B) → U b) → ((a : A) → U (f a))
```

is an [equivalence](foundation-core.equivalences.md).

We give a series of increasingly stronger conditions for a map `f` to be
`K`-connected. In particular, if `unit ∈ K`, then condition 4 recovers the usual
definition of a `K`-connected map as in Definition 5.5.1 {{#cite Rij19}}, i.e.,
as a map whose [fibers](foundation-core.fibers-of-maps.md) have
[contractible](foundation-core.contractible-types.md)
`K`-[localizations](orthogonal-factorization-systems.localizations-at-subuniverses.md).

1.  The map `f` is `K`-connected.
2.  For every `K`-valued family `U` over `B` and every map
    `u : (x : A) → U (f x)`, the type of
    [extensions](orthogonal-factorization-systems.extensions-dependent-maps.md)
    of `u` along `f` is contractible.
3.  The map `f` is
    [left orthogonal](orthogonal-factorization-systems.orthogonal-maps.md) to
    maps `h : C → B` whose fibers are in `K`.
4.  The [terminal projections](foundation.unit-type.md) of the fibers of `f` are
    `K`-[equivalences](orthogonal-factorization-systems.subuniverse-equivalences.md).
5.  The fibers of `f` are `K`-connected in the sense that for every `U` in `K`,
    the [diagonal map](foundation.diagonal-maps-of-types.md)
    `U → (fiber f y → U)` is an equivalence.
6.  Every fiber of `f` satisfies the condition that for every `U` in `K` and
    every function `u : fiber f y → U` there
    [uniquely exists](foundation.uniqueness-quantification.md) an element
    `v : U` such that `const v ~ u`.
7.  The fibers of `f` have `K`-localizations, and there
    [merely exists](foundation.existential-quantification.md) a
    `u : K(fiber f y)` such that for all `a` and `p : f a ＝ y` we have a
    [dependent identification](foundation-core.dependent-identifications.md)
    over `p`
    ```text
      u ＝ₚ^[y ↦ K(fiber f y)] (η (f a) (a , refl))
    ```
8.  The fibers of `f` have `K`-localizations, and the dependent precomposition
    map of `f` is [surjective](foundation.surjective-maps.md) at every
    `K`-valued family `U` over `B`.
9.  The fibers of `f` have `K`-localizations, and the dependent precomposition
    map of `f` has a [section](foundation-core.sections.md) at every `K`-valued
    family `U` over `B`.

If the fibers of `f` have `K`-localizations then these conditions are all
[equivalent](foundation.logical-equivalences.md). More generally we always have
that conditions 1-3 are equivalent, conditions 4-6 are equivalent, and
conditions 7-9 are equivalent.

## Definitions

### The predicate on maps of being `K`-connected

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) {A : UU l3} {B : UU l4}
  (f : A → B)
  where

  is-subuniverse-connected-map-Prop : Prop (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subuniverse-connected-map-Prop =
    Π-Prop
      ( B → type-subuniverse K)
      ( λ U → is-equiv-Prop (precomp-Π f (pr1 ∘ U)))

  is-subuniverse-connected-map : UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subuniverse-connected-map =
    (U : B → type-subuniverse K) → is-equiv (precomp-Π f (pr1 ∘ U))

  is-prop-is-subuniverse-connected-map :
    is-prop is-subuniverse-connected-map
  is-prop-is-subuniverse-connected-map =
    is-prop-type-Prop is-subuniverse-connected-map-Prop
```

### The type of `K`-connected maps between two types

```agda
subuniverse-connected-map :
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) →
  UU l3 → UU l4 → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
subuniverse-connected-map K A B =
  type-subtype (is-subuniverse-connected-map-Prop K {A} {B})

module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) {A : UU l3} {B : UU l4}
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

### The extension condition of `K`-connected maps

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  is-subuniverse-connected-map-extension-condition :
    UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subuniverse-connected-map-extension-condition =
    (U : B → type-subuniverse K) (u : (x : A) → pr1 (U (f x))) →
    is-contr (extension-dependent-type f (pr1 ∘ U) u)

  abstract
    is-prop-is-subuniverse-connected-map-extension-condition :
      is-prop is-subuniverse-connected-map-extension-condition
    is-prop-is-subuniverse-connected-map-extension-condition =
      is-prop-Π (λ U → is-prop-Π (λ u → is-property-is-contr))

  is-subuniverse-connected-map-extension-condition-Prop :
    Prop (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subuniverse-connected-map-extension-condition-Prop =
    ( is-subuniverse-connected-map-extension-condition ,
      is-prop-is-subuniverse-connected-map-extension-condition)
```

## Properties

### Equivalent characterizations of `K`-connected maps

#### Extension condition

A map `f : A → B` is `K`-connected if and only if, for every `K`-valued family
`U` over `B` and every map `u : (x : A) → U (f x)`, the type of dependent
extensions of `u` along `f` is contractible.

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  is-subuniverse-connected-map-is-subuniverse-connected-map-extension-condition :
    is-subuniverse-connected-map-extension-condition K f →
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-is-subuniverse-connected-map-extension-condition
    H U =
    is-equiv-is-contr-map
      ( λ u →
        is-contr-equiv
          ( extension-dependent-type f (pr1 ∘ U) u)
          ( compute-extension-fiber-precomp-Π f (pr1 ∘ U) u)
          ( H U u))

  is-subuniverse-connected-map-extension-condition-is-subuniverse-connected-map :
    is-subuniverse-connected-map K f →
    is-subuniverse-connected-map-extension-condition K f
  is-subuniverse-connected-map-extension-condition-is-subuniverse-connected-map
    H U u =
    is-contr-equiv'
      ( fiber (precomp-Π f (pr1 ∘ U)) u)
      ( compute-extension-fiber-precomp-Π f (pr1 ∘ U) u)
      ( is-contr-map-is-equiv (H U) u)
```

#### Contractible fiber-localization condition

Given a subuniverse `K` then a map `f` is `K`-connected if the fibers are
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
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
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

#### Fiber condition

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  is-subuniverse-connected-map-is-subuniverse-connected-fibers :
    ( (b : B) → is-subuniverse-connected K (fiber f b)) →
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-is-subuniverse-connected-fibers H =
    is-subuniverse-connected-map-is-subuniverse-equiv-terminal-map-fibers K f
      ( is-subuniverse-equiv-terminal-map-is-subuniverse-connected K ∘ H)
```

#### Constancy condition on fibers

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  is-subuniverse-connected-map-is-subuniverse-connected-const-condition-fibers :
    ( (b : B) → is-subuniverse-connected-const-condition K (fiber f b)) →
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-is-subuniverse-connected-const-condition-fibers
    H =
    is-subuniverse-connected-map-is-subuniverse-connected-fibers K f
      ( λ b →
        is-subuniverse-connected-is-subuniverse-connected-const-condition K
          ( H b))
```

#### Section condition

A map is `K`-connected if and only if its dependent precomposition maps admit
sections and the fibers have `K`-localizations.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (Kfib : B → UU l3) (η : (b : B) → fiber f b → Kfib b)
  (is-htpy-injective-precomp-η-Kfib :
    (b : B) {g h : Kfib b → Kfib b} →
    precomp (η b) (Kfib b) g ~ precomp (η b) (Kfib b) h → g ~ h)
  where

  is-contr-subuniverse-localization-fiber-has-section-precomp-Π'' :
    ( dependent-product-fiber-precomp-Π' f Kfib (λ a → η (f a) (a , refl))) →
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
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
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

is inhabited, which is in turn a slightly weaker condition than inhabitedness of
the fiber of `precomp-Π f` over the map `a ↦ η (f a) (a , refl)`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (Kfib : B → UU l3)
  (η : (b : B) → fiber f b → Kfib b)
  (is-htpy-injective-precomp-η-Kfib :
    (b : B) {g h : Kfib b → Kfib b} →
    precomp (η b) (Kfib b) g ~ precomp (η b) (Kfib b) h → g ~ h)
  where

  abstract
    is-contr-subuniverse-localization-fiber-is-inhabited-family-dependent-product-fiber-precomp-Π' :
      ( (b : B) →
        is-inhabited
          ( family-dependent-product-fiber-precomp-Π' f Kfib
            ( λ a → η (f a) (a , refl))
            ( b))) →
      ((b : B) → is-contr (Kfib b))
    is-contr-subuniverse-localization-fiber-is-inhabited-family-dependent-product-fiber-precomp-Π'
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
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  (Kfib : (b : B) → subuniverse-localization K (fiber f b))
  where

  is-contr-subuniverse-localization-fiber-is-inhabited-family-dependent-product-fiber-precomp-Π :
    ( (b : B) →
      is-inhabited
        ( family-dependent-product-fiber-precomp-Π' f
          ( type-subuniverse-localization K ∘ Kfib)
          ( λ a → unit-subuniverse-localization K (Kfib (f a)) (a , refl))
          ( b))) →
    ((b : B) → is-contr (type-subuniverse-localization K (Kfib b)))
  is-contr-subuniverse-localization-fiber-is-inhabited-family-dependent-product-fiber-precomp-Π =
    is-contr-subuniverse-localization-fiber-is-inhabited-family-dependent-product-fiber-precomp-Π'
      ( f)
      ( type-subuniverse-localization K ∘ Kfib)
      ( unit-subuniverse-localization K ∘ Kfib)
      ( λ b H →
        htpy-eq
          ( is-injective-is-equiv
            ( is-subuniverse-equiv-unit-subuniverse-localization K (Kfib b)
              ( type-subuniverse-subuniverse-localization K (Kfib b)))
            ( eq-htpy H)))

  is-subuniverse-equiv-terminal-map-fibers-is-inhabited-family-dependent-product-fiber-precomp-Π :
    ( (b : B) →
      is-inhabited
        ( family-dependent-product-fiber-precomp-Π' f
          ( type-subuniverse-localization K ∘ Kfib)
          ( λ a → unit-subuniverse-localization K (Kfib (f a)) (a , refl))
          ( b))) →
    (b : B) → is-subuniverse-equiv K (terminal-map (fiber f b))
  is-subuniverse-equiv-terminal-map-fibers-is-inhabited-family-dependent-product-fiber-precomp-Π
    s b =
    is-subuniverse-equiv-comp K
      ( terminal-map (type-subuniverse-localization K (Kfib b)))
      ( unit-subuniverse-localization K (Kfib b))
      ( is-subuniverse-equiv-unit-subuniverse-localization K (Kfib b))
      ( is-subuniverse-equiv-is-equiv K
        ( terminal-map (type-subuniverse-localization K (Kfib b)))
        ( is-equiv-terminal-map-is-contr
          ( is-contr-subuniverse-localization-fiber-is-inhabited-family-dependent-product-fiber-precomp-Π
            s b)))

  is-subuniverse-connected-map-is-inhabited-family-dependent-product-fiber-precomp-Π :
    ( (b : B) →
      is-inhabited
        ( family-dependent-product-fiber-precomp-Π' f
          ( type-subuniverse-localization K ∘ Kfib)
          ( λ a → unit-subuniverse-localization K (Kfib (f a)) (a , refl))
          ( b))) →
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-is-inhabited-family-dependent-product-fiber-precomp-Π
    Fη =
    is-subuniverse-connected-map-is-subuniverse-equiv-terminal-map-fibers K f
      ( is-subuniverse-equiv-terminal-map-fibers-is-inhabited-family-dependent-product-fiber-precomp-Π
        ( Fη))

  is-contr-subuniverse-localization-fiber-is-surjective-precomp-Π :
    ((U : B → type-subuniverse K) → is-surjective (precomp-Π f (pr1 ∘ U))) →
    ((b : B) → is-contr (pr1 (Kfib b)))
  is-contr-subuniverse-localization-fiber-is-surjective-precomp-Π H =
    is-contr-subuniverse-localization-fiber-is-inhabited-fiber-precomp-Π f
      ( type-subuniverse-localization K ∘ Kfib)
      ( unit-subuniverse-localization K ∘ Kfib)
      ( λ b H →
        htpy-eq
          ( is-injective-is-equiv
            ( is-subuniverse-equiv-unit-subuniverse-localization K (Kfib b)
              ( type-subuniverse-subuniverse-localization K (Kfib b)))
            ( eq-htpy H)))
      ( H ( type-subuniverse-subuniverse-localization K ∘ Kfib)
          ( λ a → unit-subuniverse-localization K (Kfib (f a)) (a , refl)))

  is-subuniverse-equiv-terminal-map-fibers-is-surjective-precomp-Π :
    ((U : B → type-subuniverse K) → is-surjective (precomp-Π f (pr1 ∘ U))) →
    (b : B) → is-subuniverse-equiv K (terminal-map (fiber f b))
  is-subuniverse-equiv-terminal-map-fibers-is-surjective-precomp-Π H b =
    is-subuniverse-equiv-comp K
      ( terminal-map (type-subuniverse-localization K (Kfib b)))
      ( unit-subuniverse-localization K (Kfib b))
      ( is-subuniverse-equiv-unit-subuniverse-localization K (Kfib b))
      ( is-subuniverse-equiv-is-equiv K
        ( terminal-map (type-subuniverse-localization K (Kfib b)))
        ( is-equiv-terminal-map-is-contr
          ( is-contr-subuniverse-localization-fiber-is-surjective-precomp-Π
              H b)))

  is-subuniverse-connected-map-is-surjective-precomp-Π :
    ((U : B → type-subuniverse K) → is-surjective (precomp-Π f (pr1 ∘ U))) →
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-is-surjective-precomp-Π H =
    is-subuniverse-connected-map-is-subuniverse-equiv-terminal-map-fibers K f
      ( is-subuniverse-equiv-terminal-map-fibers-is-surjective-precomp-Π H)
```

### Characterizing equality of `K`-connected maps

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) {A : UU l3} {B : UU l4}
  where

  htpy-subuniverse-connected-map :
    (f g : subuniverse-connected-map K A B) → UU (l3 ⊔ l4)
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

  htpy-eq-subuniverse-connected-map :
    (f g : subuniverse-connected-map K A B) →
    f ＝ g → htpy-subuniverse-connected-map f g
  htpy-eq-subuniverse-connected-map f g H = htpy-eq (ap pr1 H)

  is-equiv-htpy-eq-subuniverse-connected-map :
    (f g : subuniverse-connected-map K A B) →
    is-equiv (htpy-eq-subuniverse-connected-map f g)
  is-equiv-htpy-eq-subuniverse-connected-map f =
    fundamental-theorem-id
      ( is-torsorial-htpy-subuniverse-connected-map f)
      ( htpy-eq-subuniverse-connected-map f)

  extensionality-subuniverse-connected-map :
    (f g : subuniverse-connected-map K A B) →
    (f ＝ g) ≃ htpy-subuniverse-connected-map f g
  pr1 (extensionality-subuniverse-connected-map f g) =
    htpy-eq-subuniverse-connected-map f g
  pr2 (extensionality-subuniverse-connected-map f g) =
    is-equiv-htpy-eq-subuniverse-connected-map f g

  eq-htpy-subuniverse-connected-map :
    (f g : subuniverse-connected-map K A B) →
    htpy-subuniverse-connected-map f g → (f ＝ g)
  eq-htpy-subuniverse-connected-map f g =
    map-inv-equiv (extensionality-subuniverse-connected-map f g)
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
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2) {A : UU l3} {B : UU l4}
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
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : A → B)
  where

  is-subuniverse-equiv-is-subuniverse-connected-map :
    is-subuniverse-connected-map K f → is-subuniverse-equiv K f
  is-subuniverse-equiv-is-subuniverse-connected-map F U = F (λ _ → U)
```

### The composition of two `K`-connected maps is `K`-connected

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {C : UU l5}
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
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {C : UU l5}
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

### `K`-connected maps are closed under cobase change

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (K : subuniverse l1 l2)
  {S : UU l3} {A : UU l4} {B : UU l5}
  (f : S → A) (g : S → B) {X : UU l6} (c : cocone f g X)
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

> This remains to be formalized.

The formalization below takes a shortcut via the fibers.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {C : UU l5} {D : UU l6}
  {f : A → B} {g : C → D} (R : f retract-of-map g)
  where

  is-subuniverse-connected-map-retract-map' :
    ((y : D) → is-subuniverse-connected K (fiber g y)) →
    is-subuniverse-connected-map K f
  is-subuniverse-connected-map-retract-map' H =
    is-subuniverse-connected-map-is-subuniverse-connected-fibers K f
    ( λ b →
      is-subuniverse-connected-retract K
        ( retract-fiber-retract-map f g R b)
        ( H (map-codomain-inclusion-retract-map f g R b)))
```

### The total map induced by a family of maps is `K`-connected if and only if all maps in the family are `K`-connected

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : A → UU l4} {C : A → UU l5}
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
```

### Coproducts of `K`-connected maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} {A' : UU l5} {B' : UU l6}
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
  {l1 l2 l3 l4 : Level} (K : subuniverse l1 l2)
  {A : UU l3} {B : UU l4} (f : subuniverse-connected-map K A B)
  (P : B → UU l1)
  where

  map-Σ-map-base-subuniverse-connected-map :
    Σ A (P ∘ map-subuniverse-connected-map K f) → Σ B P
  map-Σ-map-base-subuniverse-connected-map =
    map-Σ-map-base (map-subuniverse-connected-map K f) P

  is-subuniverse-equiv-map-Σ-map-base-subuniverse-connected-map :
    ((V : UU l1) (U : type-subuniverse K) → is-in-subuniverse K (V → pr1 U)) →
    is-subuniverse-equiv K map-Σ-map-base-subuniverse-connected-map
  is-subuniverse-equiv-map-Σ-map-base-subuniverse-connected-map H U =
    is-equiv-source-is-equiv-target-equiv-arrow
      ( precomp map-Σ-map-base-subuniverse-connected-map (pr1 U))
      ( precomp-Π (map-subuniverse-connected-map K f) (λ y → (b : P y) → pr1 U))
      ( equiv-ev-pair , equiv-ev-pair , refl-htpy)
      ( is-subuniverse-connected-map-subuniverse-connected-map K f
        ( λ y → ((P y → pr1 U) , H (P y) U)))
```

## References

{{#bibliography}}
