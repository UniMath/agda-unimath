# The double negation image of a map

```agda
module foundation.double-negation-images where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.fundamental-theorem-of-identity-types
open import foundation.hilbert-epsilon-operators-maps
open import foundation.slice
open import foundation.split-surjective-maps
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import logic.double-negation-dense-maps
open import logic.double-negation-eliminating-maps
open import logic.double-negation-stable-embeddings
```

</details>

## Idea

The
{{#concept "double negation image" Disambiguation="of a map" Agda=double-negation-im}}
of `f : A → B` is the essentially unique type that
[factorizes](orthogonal-factorization-systems.factorizations-of-maps.md) `f` as
a [double negation dense map](logic.double-negation-dense-maps.md) followed by a
[double negation stable embedding](logic.double-negation-stable-embeddings.md).
I.e., the double negation image `im'f` of `f` fits into a commuting triangle

```text
         im'f
        ∧    \
    l /        \ r
    /      f     ∨
  A -------------> B
```

such that `l` is double negation dense, i.e., its
[fibers](foundation-core.fibers-of-maps.md) are
[nonempty](foundation.double-negation.md), and `r` is a double negation stable
embedding, i.e., its fibers are [propositions](foundation-core.propositions.md)
that satisfy the property that if they are nonempty then they are inhabited.

This factorization is unique in the sense that any other commuting triangle

```text
          X
        ∧   \
    l'/       \ r'
    /     f     ∨
  A ------------> B
```

is uniquely equivalent to the double negation image factorization in a coherent
manner. This is a direct consequence of the fact that double negation is a
modality, which is shown in
[`foundation.double-negation-modality`](foundation.double-negation-modality.md).

The double negation image factorization is in one sense an approximation to the
[image factorization](foundation.images.md) that satisfies a restricted
universal property which only applies to
[negative statements](foundation-core.negation.md), and does not rely on the
existence of
[propositional truncations](foundation.propositional-truncations.md). On the
other hand, the double negation image inclusion `r` satisfies the additional
property of being double negation stable, compared to the image inclusion.

## Definitions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  subtype-double-negation-im : subtype (l1 ⊔ l2) X
  subtype-double-negation-im x = double-negation-type-Prop (fiber f x)

  is-in-double-negation-im : X → UU (l1 ⊔ l2)
  is-in-double-negation-im = is-in-subtype subtype-double-negation-im

  double-negation-im : UU (l1 ⊔ l2)
  double-negation-im = type-subtype subtype-double-negation-im

  inclusion-double-negation-im : double-negation-im → X
  inclusion-double-negation-im = inclusion-subtype subtype-double-negation-im

  map-unit-double-negation-im : A → double-negation-im
  map-unit-double-negation-im a = (f a , intro-double-negation (a , refl))

  triangle-unit-double-negation-im :
    coherence-triangle-maps
      ( f)
      ( inclusion-double-negation-im)
      ( map-unit-double-negation-im)
  triangle-unit-double-negation-im a = refl

  unit-double-negation-im : hom-slice f inclusion-double-negation-im
  pr1 unit-double-negation-im = map-unit-double-negation-im
  pr2 unit-double-negation-im = triangle-unit-double-negation-im
```

## Properties

### We characterize the identity type of `double-negation-im f`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  Eq-double-negation-im : double-negation-im f → double-negation-im f → UU l1
  Eq-double-negation-im x y = (pr1 x ＝ pr1 y)

  refl-Eq-double-negation-im :
    (x : double-negation-im f) → Eq-double-negation-im x x
  refl-Eq-double-negation-im x = refl

  Eq-eq-double-negation-im :
    (x y : double-negation-im f) → x ＝ y → Eq-double-negation-im x y
  Eq-eq-double-negation-im x .x refl = refl-Eq-double-negation-im x

  abstract
    is-torsorial-Eq-double-negation-im :
      (x : double-negation-im f) → is-torsorial (Eq-double-negation-im x)
    is-torsorial-Eq-double-negation-im x =
      is-torsorial-Eq-subtype
        ( is-torsorial-Id (pr1 x))
        ( is-prop-is-in-subtype (subtype-double-negation-im f))
        ( pr1 x)
        ( refl)
        ( pr2 x)

  abstract
    is-equiv-Eq-eq-double-negation-im :
      (x y : double-negation-im f) → is-equiv (Eq-eq-double-negation-im x y)
    is-equiv-Eq-eq-double-negation-im x =
      fundamental-theorem-id
        ( is-torsorial-Eq-double-negation-im x)
        ( Eq-eq-double-negation-im x)

  equiv-Eq-eq-double-negation-im :
    (x y : double-negation-im f) → (x ＝ y) ≃ Eq-double-negation-im x y
  equiv-Eq-eq-double-negation-im x y =
    ( Eq-eq-double-negation-im x y , is-equiv-Eq-eq-double-negation-im x y)

  eq-Eq-double-negation-im :
    (x y : double-negation-im f) → Eq-double-negation-im x y → x ＝ y
  eq-Eq-double-negation-im x y =
    map-inv-equiv (equiv-Eq-eq-double-negation-im x y)
```

### The unit map of the double negation image is double negation dense

```agda
abstract
  is-double-negation-dense-unit-double-negation-im :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-double-negation-dense-map (map-unit-double-negation-im f)
  is-double-negation-dense-unit-double-negation-im f (y , nnq) np =
    nnq
      ( λ p →
        np
          ( pr1 p ,
            eq-Eq-double-negation-im f
              ( map-unit-double-negation-im f (pr1 p)) (y , nnq) (pr2 p)))
```

### The double negation image inclusion is a double negation stable embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  is-emb-inclusion-double-negation-im :
    is-emb (inclusion-double-negation-im f)
  is-emb-inclusion-double-negation-im =
    is-emb-inclusion-subtype (subtype-double-negation-im f)

  emb-double-negation-im : double-negation-im f ↪ X
  emb-double-negation-im =
    ( inclusion-double-negation-im f , is-emb-inclusion-double-negation-im)

  is-injective-inclusion-double-negation-im :
    is-injective (inclusion-double-negation-im f)
  is-injective-inclusion-double-negation-im =
    is-injective-is-emb is-emb-inclusion-double-negation-im

  is-double-negation-eliminating-map-inclusion-double-negation-im :
    is-double-negation-eliminating-map (inclusion-double-negation-im f)
  is-double-negation-eliminating-map-inclusion-double-negation-im x nnip =
    ( ( x ,
        ( λ np →
          nnip
            ( λ ip →
              is-double-negation-dense-unit-double-negation-im f
                ( pr1 ip)
                ( λ ηq →
                  np
                  ( pr1 ηq ,
                    ap (inclusion-double-negation-im f) (pr2 ηq) ∙ pr2 ip))))) ,
      ( refl))

  double-negation-eliminating-map-inclusion-double-negation-im :
    double-negation-im f →¬¬ X
  double-negation-eliminating-map-inclusion-double-negation-im =
    ( inclusion-double-negation-im f ,
      is-double-negation-eliminating-map-inclusion-double-negation-im)

  is-double-negation-stable-emb-inclusion-double-negation-im :
    is-double-negation-stable-emb (inclusion-double-negation-im f)
  is-double-negation-stable-emb-inclusion-double-negation-im =
    ( is-emb-inclusion-double-negation-im ,
      is-double-negation-eliminating-map-inclusion-double-negation-im)

  double-negation-stable-emb-double-negation-im : double-negation-im f ↪¬¬ X
  double-negation-stable-emb-double-negation-im =
    ( inclusion-double-negation-im f ,
      is-double-negation-stable-emb-inclusion-double-negation-im)

  ε-operator-map-inclusion-double-negation-im :
    ε-operator-map (inclusion-double-negation-im f)
  ε-operator-map-inclusion-double-negation-im =
    ε-operator-double-negation-eliminating-map
      ( double-negation-eliminating-map-inclusion-double-negation-im)
```

### The double negation image of a map into a truncated type is truncated

```agda
abstract
  is-trunc-double-negation-im :
    {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A → X) →
    is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (double-negation-im f)
  is-trunc-double-negation-im k f = is-trunc-emb k (emb-double-negation-im f)

double-negation-im-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) (X : Truncated-Type l1 (succ-𝕋 k)) {A : UU l2}
  (f : A → type-Truncated-Type X) → Truncated-Type (l1 ⊔ l2) (succ-𝕋 k)
double-negation-im-Truncated-Type k X f =
  ( double-negation-im f ,
    is-trunc-double-negation-im k f (is-trunc-type-Truncated-Type X))
```

### The double negation image of a map into a proposition is a proposition

```agda
abstract
  is-prop-double-negation-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-prop X → is-prop (double-negation-im f)
  is-prop-double-negation-im = is-trunc-double-negation-im neg-two-𝕋

double-negation-im-Prop :
  {l1 l2 : Level} (X : Prop l1) {A : UU l2} →
  (A → type-Prop X) → Prop (l1 ⊔ l2)
double-negation-im-Prop = double-negation-im-Truncated-Type neg-two-𝕋
```

### The double negation image of a map into a set is a set

```agda
abstract
  is-set-double-negation-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-set X → is-set (double-negation-im f)
  is-set-double-negation-im = is-trunc-double-negation-im neg-one-𝕋

double-negation-im-Set :
  {l1 l2 : Level} (X : Set l1) {A : UU l2} →
  (A → type-Set X) → Set (l1 ⊔ l2)
double-negation-im-Set = double-negation-im-Truncated-Type neg-one-𝕋
```

### The double negation image of a map into a 1-type is a 1-type

```agda
abstract
  is-1-type-double-negation-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-1-type X → is-1-type (double-negation-im f)
  is-1-type-double-negation-im = is-trunc-double-negation-im zero-𝕋

double-negation-im-1-Type :
  {l1 l2 : Level} (X : 1-Type l1) {A : UU l2}
  (f : A → type-1-Type X) → 1-Type (l1 ⊔ l2)
double-negation-im-1-Type = double-negation-im-Truncated-Type zero-𝕋
```

### Injective double negation eliminating maps are embeddings

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} {f : A → X}
  where

  map-section-map-unit-double-negation-im :
    is-double-negation-eliminating-map f → double-negation-im f → A
  map-section-map-unit-double-negation-im K (y , p) = pr1 (K y p)

  is-section-map-section-map-unit-double-negation-im :
    (K : is-double-negation-eliminating-map f) →
    is-section
      ( map-unit-double-negation-im f)
      ( map-section-map-unit-double-negation-im K)
  is-section-map-section-map-unit-double-negation-im K (y , p) =
    is-injective-inclusion-double-negation-im f (pr2 (K y p))

  section-map-unit-double-negation-im :
    is-double-negation-eliminating-map f →
    section (map-unit-double-negation-im f)
  section-map-unit-double-negation-im K =
    ( map-section-map-unit-double-negation-im K ,
      is-section-map-section-map-unit-double-negation-im K)

  is-equiv-map-unit-double-negation-im :
    is-double-negation-eliminating-map f →
    is-injective f →
    is-equiv (map-unit-double-negation-im f)
  is-equiv-map-unit-double-negation-im K H =
    is-equiv-is-injective
      ( section-map-unit-double-negation-im K)
      ( is-injective-right-factor
        ( inclusion-double-negation-im f)
        ( map-unit-double-negation-im f)
        ( H))

  is-emb-is-injective-is-double-negation-eliminating-map :
    is-double-negation-eliminating-map f → is-injective f → is-emb f
  is-emb-is-injective-is-double-negation-eliminating-map K H =
    is-emb-comp
      ( inclusion-double-negation-im f)
      ( map-unit-double-negation-im f)
      ( is-emb-inclusion-double-negation-im f)
      ( is-emb-is-equiv (is-equiv-map-unit-double-negation-im K H))
```

## See also

- [The double negation modality](foundation.double-negation-modality.md)
