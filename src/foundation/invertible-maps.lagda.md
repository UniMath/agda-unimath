# Invertible maps

```agda
module foundation.invertible-maps where

open import foundation-core.invertible-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.homotopy-induction
open import foundation.postcomposition-functions
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.coherently-invertible-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import synthetic-homotopy-theory.free-loops
```

</details>

## Properties

### Characterizing equality of invertible maps

#### Characterizing equality of `is-inverse`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  htpy-is-inverse : (s t : is-inverse f g) → UU (l1 ⊔ l2)
  htpy-is-inverse s t = (pr1 s ~ pr1 t) × (pr2 s ~ pr2 t)

  extensionality-is-inverse :
    {s t : is-inverse f g} → (s ＝ t) ≃ htpy-is-inverse s t
  extensionality-is-inverse {s} {t} =
    equiv-product equiv-funext equiv-funext ∘e equiv-pair-eq s t

  htpy-eq-is-inverse : {s t : is-inverse f g} → s ＝ t → htpy-is-inverse s t
  htpy-eq-is-inverse = map-equiv extensionality-is-inverse

  eq-htpy-is-inverse : {s t : is-inverse f g} → htpy-is-inverse s t → s ＝ t
  eq-htpy-is-inverse = map-inv-equiv extensionality-is-inverse
```

#### Characterizing equality of `is-invertible`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-htpy-is-invertible :
    (s t : is-invertible f) →
    map-inv-is-invertible s ~ map-inv-is-invertible t → UU (l1 ⊔ l2)
  coherence-htpy-is-invertible s t H =
    ( coherence-htpy-section {f = f}
      ( section-is-invertible s)
      ( section-is-invertible t)
      ( H)) ×
    ( coherence-htpy-retraction
      ( retraction-is-invertible s)
      ( retraction-is-invertible t)
      ( H))

  htpy-is-invertible : (s t : is-invertible f) → UU (l1 ⊔ l2)
  htpy-is-invertible s t =
    Σ ( map-inv-is-invertible s ~ map-inv-is-invertible t)
      ( coherence-htpy-is-invertible s t)

  refl-htpy-is-invertible : (s : is-invertible f) → htpy-is-invertible s s
  pr1 (refl-htpy-is-invertible s) = refl-htpy
  pr1 (pr2 (refl-htpy-is-invertible s)) = refl-htpy
  pr2 (pr2 (refl-htpy-is-invertible s)) = refl-htpy

  htpy-eq-is-invertible :
    (s t : is-invertible f) → s ＝ t → htpy-is-invertible s t
  htpy-eq-is-invertible s .s refl = refl-htpy-is-invertible s

  is-torsorial-htpy-is-invertible :
    (s : is-invertible f) → is-torsorial (htpy-is-invertible s)
  is-torsorial-htpy-is-invertible s =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-inv-is-invertible s))
      ( map-inv-is-invertible s , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (is-section-map-inv-is-invertible s))
        ( is-section-map-inv-is-invertible s , refl-htpy)
        (is-torsorial-htpy (is-retraction-map-inv-is-invertible s)))

  is-equiv-htpy-eq-is-invertible :
    (s t : is-invertible f) → is-equiv (htpy-eq-is-invertible s t)
  is-equiv-htpy-eq-is-invertible s =
    fundamental-theorem-id
      ( is-torsorial-htpy-is-invertible s)
      ( htpy-eq-is-invertible s)

  extensionality-is-invertible :
    (s t : is-invertible f) → (s ＝ t) ≃ (htpy-is-invertible s t)
  pr1 (extensionality-is-invertible s t) = htpy-eq-is-invertible s t
  pr2 (extensionality-is-invertible s t) = is-equiv-htpy-eq-is-invertible s t

  eq-htpy-is-invertible :
    (s t : is-invertible f) → htpy-is-invertible s t → s ＝ t
  eq-htpy-is-invertible s t = map-inv-equiv (extensionality-is-invertible s t)
```

#### Characterizing equality of `invertible-map`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-htpy-invertible-map :
    (s t : invertible-map A B) →
    map-invertible-map s ~ map-invertible-map t →
    map-inv-invertible-map s ~ map-inv-invertible-map t → UU (l1 ⊔ l2)
  coherence-htpy-invertible-map s t H I =
    ( coherence-triangle-homotopies
      ( is-section-map-inv-invertible-map s)
      ( is-section-map-inv-invertible-map t)
      ( horizontal-concat-htpy H I)) ×
    ( coherence-triangle-homotopies
      ( is-retraction-map-inv-invertible-map s)
      ( is-retraction-map-inv-invertible-map t)
      ( horizontal-concat-htpy I H))

  htpy-invertible-map : (s t : invertible-map A B) → UU (l1 ⊔ l2)
  htpy-invertible-map s t =
    Σ ( map-invertible-map s ~ map-invertible-map t)
      ( λ H →
        Σ ( map-inv-invertible-map s ~ map-inv-invertible-map t)
          ( coherence-htpy-invertible-map s t H))

  refl-htpy-invertible-map : (s : invertible-map A B) → htpy-invertible-map s s
  pr1 (refl-htpy-invertible-map s) = refl-htpy
  pr1 (pr2 (refl-htpy-invertible-map s)) = refl-htpy
  pr1 (pr2 (pr2 (refl-htpy-invertible-map s))) = refl-htpy
  pr2 (pr2 (pr2 (refl-htpy-invertible-map s))) = refl-htpy

  htpy-eq-invertible-map :
    (s t : invertible-map A B) → s ＝ t → htpy-invertible-map s t
  htpy-eq-invertible-map s .s refl = refl-htpy-invertible-map s

  is-torsorial-htpy-invertible-map :
    (s : invertible-map A B) → is-torsorial (htpy-invertible-map s)
  is-torsorial-htpy-invertible-map s =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-invertible-map s))
      ( map-invertible-map s , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-inv-invertible-map s))
        ( map-inv-invertible-map s , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy (is-section-map-inv-invertible-map s))
          ( is-section-map-inv-invertible-map s , refl-htpy)
          ( is-torsorial-htpy (is-retraction-map-inv-invertible-map s))))

  is-equiv-htpy-eq-invertible-map :
    (s t : invertible-map A B) → is-equiv (htpy-eq-invertible-map s t)
  is-equiv-htpy-eq-invertible-map s =
    fundamental-theorem-id
      ( is-torsorial-htpy-invertible-map s)
      ( htpy-eq-invertible-map s)

  extensionality-invertible-map :
    (s t : invertible-map A B) → (s ＝ t) ≃ (htpy-invertible-map s t)
  pr1 (extensionality-invertible-map s t) = htpy-eq-invertible-map s t
  pr2 (extensionality-invertible-map s t) = is-equiv-htpy-eq-invertible-map s t

  eq-htpy-invertible-map :
    (s t : invertible-map A B) → htpy-invertible-map s t → s ＝ t
  eq-htpy-invertible-map s t = map-inv-equiv (extensionality-invertible-map s t)
```

### If the domains are `k`-truncated, then the type of inverses is `k`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  is-trunc-is-inverse :
    (f : A → B) (g : B → A) →
    is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) B →
    is-trunc k (is-inverse f g)
  is-trunc-is-inverse f g is-trunc-A is-trunc-B =
    is-trunc-product k
      ( is-trunc-Π k (λ x → is-trunc-B (f (g x)) x))
      ( is-trunc-Π k (λ x → is-trunc-A (g (f x)) x))

  is-trunc-is-invertible :
    (f : A → B) →
    is-trunc k A → is-trunc (succ-𝕋 k) B →
    is-trunc k (is-invertible f)
  is-trunc-is-invertible f is-trunc-A is-trunc-B =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-A)
      ( λ g →
        is-trunc-is-inverse f g
          ( is-trunc-succ-is-trunc k is-trunc-A)
          ( is-trunc-B))

  is-trunc-invertible-map :
    is-trunc k A → is-trunc k B →
    is-trunc k (invertible-map A B)
  is-trunc-invertible-map is-trunc-A is-trunc-B =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-B)
      ( λ f →
        is-trunc-is-invertible f
          ( is-trunc-A)
          ( is-trunc-succ-is-trunc k is-trunc-B))
```

### The type `is-invertible id` is equivalent to `id ~ id`

```agda
is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  (id {A = A} ~ id {A = A}) → is-invertible (id {A = A})
pr1 (is-invertible-id-htpy-id-id A H) = id
pr1 (pr2 (is-invertible-id-htpy-id-id A H)) = refl-htpy
pr2 (pr2 (is-invertible-id-htpy-id-id A H)) = H

triangle-is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  ( is-invertible-id-htpy-id-id A) ~
    ( ( map-associative-Σ) ∘
      ( map-inv-left-unit-law-Σ-is-contr
        { B = λ s → (pr1 s ∘ id) ~ id}
        ( is-contr-section-is-equiv (is-equiv-id {_} {A}))
        ( pair id refl-htpy)))
triangle-is-invertible-id-htpy-id-id A H = refl

abstract
  is-equiv-is-invertible-id-htpy-id-id :
    {l : Level} (A : UU l) → is-equiv (is-invertible-id-htpy-id-id A)
  is-equiv-is-invertible-id-htpy-id-id A =
    is-equiv-left-map-triangle
      ( is-invertible-id-htpy-id-id A)
      ( map-associative-Σ)
      ( map-inv-left-unit-law-Σ-is-contr
        ( is-contr-section-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( triangle-is-invertible-id-htpy-id-id A)
      ( is-equiv-map-inv-left-unit-law-Σ-is-contr
        ( is-contr-section-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( is-equiv-map-associative-Σ)
```

### The type of invertible maps is equivalent to the type of free loops on equivalences

#### The type of invertible equivalences is equivalent to the type of invertible maps

**Proof:** Since every invertible map is an equivalence, the `Σ`-type of
invertible maps which are equivalences forms a full subtype of the type of
invertible maps. Swapping the order of `Σ`-types then shows that the `Σ`-type of
invertible maps which are equivalences is equivalent to the `Σ`-type of
equivalences which are invertible.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-equiv-prop-is-invertible : (invertible-map A B) → Prop (l1 ⊔ l2)
  is-equiv-prop-is-invertible = is-equiv-Prop ∘ map-invertible-map

  is-full-subtype-is-equiv-prop-is-invertible :
    is-full-subtype is-equiv-prop-is-invertible
  is-full-subtype-is-equiv-prop-is-invertible =
    is-equiv-is-invertible' ∘ is-invertible-map-invertible-map

  equiv-invertible-equivalence-invertible-map :
    Σ (A ≃ B) (is-invertible ∘ map-equiv) ≃ invertible-map A B
  equiv-invertible-equivalence-invertible-map =
    ( equiv-inclusion-is-full-subtype
      ( is-equiv-prop-is-invertible)
      ( is-full-subtype-is-equiv-prop-is-invertible)) ∘e
    ( equiv-right-swap-Σ)
```

#### The type of free loops on equivalences is equivalent to the type of invertible equivalences

**Proof:** First, associating the order of `Σ`-types shows that a function being
invertible is equivalent to it having a section, such that this section is also
its retraction. Now, since equivalences have a contractible type of sections, a
proof of invertibility of the underlying map `f` of an equivalence contracts to
just a single homotopy `g ∘ f ~ id`, showing that a section `g` of `f` is also
its retraction. As `g` is a section, composing on the left with `f` and
canceling `f ∘ g` yields a loop `f ~ f`. By equivalence extensionality, this
loop may be lifted to a loop on the entire equivalence.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-is-retraction-section-is-invertible :
    (f : A → B) →
    Σ (section f) (λ g → (map-section f g) ∘ f ~ id) ≃ is-invertible f
  equiv-is-retraction-section-is-invertible f = associative-Σ

  equiv-free-loop-equivalence-invertible-equivalence :
    free-loop (A ≃ B) ≃ Σ (A ≃ B) (is-invertible ∘ map-equiv)
  equiv-free-loop-equivalence-invertible-equivalence =
    ( equiv-tot
      ( equiv-is-retraction-section-is-invertible ∘ map-equiv)) ∘e
    ( equiv-tot
      ( λ f →
        ( inv-left-unit-law-Σ-is-contr
          ( is-contr-section-is-equiv (is-equiv-map-equiv f))
          ( section-is-equiv (is-equiv-map-equiv f))) ∘e
        ( inv-equiv
          ( equiv-htpy-postcomp-htpy
            ( f)
            ( map-section-is-equiv (is-equiv-map-equiv f) ∘ map-equiv f)
            ( id))) ∘e
        ( equiv-concat-htpy
          ( is-section-map-section-map-equiv f ·r map-equiv f)
          ( map-equiv f)))) ∘e
    ( equiv-tot (λ f → extensionality-equiv f f))
```

#### The equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-free-loop-equivalence-invertible-map :
    free-loop (A ≃ B) ≃ invertible-map A B
  equiv-free-loop-equivalence-invertible-map =
    equiv-invertible-equivalence-invertible-map ∘e
    equiv-free-loop-equivalence-invertible-equivalence
```

### The action of invertible maps on identifications is invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-invertible f) {x y : A}
  where

  is-invertible-ap-is-invertible : is-invertible (ap f {x} {y})
  is-invertible-ap-is-invertible =
    is-invertible-ap-is-coherently-invertible
      ( is-coherently-invertible-is-invertible H)
```

## See also

- For the coherent notion of invertible maps see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
