# The image of an embedding

```agda
module foundation.images-embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.powersets
open import foundation.propositional-maps
open import foundation.propositional-truncations
open import foundation.slice
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.order-preserving-maps-posets
```

</details>

## Idea

The {{#concept "image" Disambiguation="of an embedding" Agda=im-emb}} of an
[embedding](foundation-core.embeddings.md) is a type that satisfies the
[universal property of the image](foundation.universal-property-image.md) of a
map.

## Definitions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A ↪ X)
  where

  subtype-im-emb : subtype (l1 ⊔ l2) X
  subtype-im-emb x = (fiber (map-emb f) x , is-prop-map-emb f x)

  is-in-subtype-im-emb : X → UU (l1 ⊔ l2)
  is-in-subtype-im-emb = is-in-subtype subtype-im-emb

  im-emb : UU (l1 ⊔ l2)
  im-emb = type-subtype subtype-im-emb

  inclusion-im-emb : im-emb → X
  inclusion-im-emb = inclusion-subtype subtype-im-emb

  map-unit-im-emb : A → im-emb
  pr1 (map-unit-im-emb a) = map-emb f a
  pr2 (map-unit-im-emb a) = a , refl

  triangle-unit-im-emb :
    coherence-triangle-maps (map-emb f) inclusion-im-emb map-unit-im-emb
  triangle-unit-im-emb a = refl

  unit-im-emb : hom-slice (map-emb f) inclusion-im-emb
  pr1 unit-im-emb = map-unit-im-emb
  pr2 unit-im-emb = triangle-unit-im-emb
```

### The direct image operator on powersets

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A ↪ X)
  where

  direct-image-hom-emb-powerset :
    hom-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( powerset-Large-Poset A)
      ( powerset-Large-Poset X)
  direct-image-hom-emb-powerset =
    make-hom-Large-Preorder
      ( λ P i → Σ-Prop (subtype-im-emb f i) (λ x → P (pr1 x)))
      ( λ P Q x y w → pr1 w , x (pr1 (pr1 w)) (pr2 w))

  direct-image-hom-emb-powerset' :
    {l : Level} →
    hom-Poset (powerset-Poset l A) (powerset-Poset (l1 ⊔ l2 ⊔ l) X)
  direct-image-hom-emb-powerset' {l} =
    ( hom-poset-hom-Large-Poset
      ( powerset-Large-Poset A)
      ( powerset-Large-Poset X)
      ( direct-image-hom-emb-powerset)
      ( l))
```

## Properties

### We characterize the identity type of `im-emb f`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A ↪ X)
  where

  Eq-im-emb : im-emb f → im-emb f → UU l1
  Eq-im-emb x y = (pr1 x ＝ pr1 y)

  refl-Eq-im-emb : (x : im-emb f) → Eq-im-emb x x
  refl-Eq-im-emb x = refl

  Eq-eq-im-emb : (x y : im-emb f) → x ＝ y → Eq-im-emb x y
  Eq-eq-im-emb x .x refl = refl-Eq-im-emb x

  abstract
    is-torsorial-Eq-im-emb :
      (x : im-emb f) → is-torsorial (Eq-im-emb x)
    is-torsorial-Eq-im-emb x =
      is-torsorial-Eq-subtype
        ( is-torsorial-Id (pr1 x))
        ( is-prop-map-emb f)
        ( pr1 x)
        ( refl)
        ( pr2 x)

  abstract
    is-equiv-Eq-eq-im-emb : (x y : im-emb f) → is-equiv (Eq-eq-im-emb x y)
    is-equiv-Eq-eq-im-emb x =
      fundamental-theorem-id
        ( is-torsorial-Eq-im-emb x)
        ( Eq-eq-im-emb x)

  equiv-Eq-eq-im-emb : (x y : im-emb f) → (x ＝ y) ≃ Eq-im-emb x y
  pr1 (equiv-Eq-eq-im-emb x y) = Eq-eq-im-emb x y
  pr2 (equiv-Eq-eq-im-emb x y) = is-equiv-Eq-eq-im-emb x y

  eq-Eq-im-emb : (x y : im-emb f) → Eq-im-emb x y → x ＝ y
  eq-Eq-im-emb x y = map-inv-is-equiv (is-equiv-Eq-eq-im-emb x y)
```

### The image inclusion is an embedding

```agda
abstract
  is-emb-inclusion-im-emb :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A ↪ X) →
    is-emb (inclusion-im-emb f)
  is-emb-inclusion-im-emb f =
    is-emb-inclusion-subtype (λ x → fiber (map-emb f) x , is-prop-map-emb f x)

emb-im-emb :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A ↪ X) → im-emb f ↪ X
pr1 (emb-im-emb f) = inclusion-im-emb f
pr2 (emb-im-emb f) = is-emb-inclusion-im-emb f
```

### The image inclusion is injective

```agda
abstract
  is-injective-inclusion-im-emb :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A ↪ X) →
    is-injective (inclusion-im-emb f)
  is-injective-inclusion-im-emb f =
    is-injective-is-emb (is-emb-inclusion-im-emb f)
```

### The unit map of the image is surjective

```text
abstract
  is-surjective-map-unit-im-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ B) →
    is-surjective (map-unit-im-emb f)
  is-surjective-map-unit-im-emb f (y , z) =
    apply-universal-property-trunc-Prop z
      ( trunc-Prop (fiber (map-unit-im-emb f) (y , z)))
      ( α)
    where
    α : fiber (map-emb f) y → type-Prop (trunc-Prop (fiber (map-unit-im-emb f) (y , z)))
    α (x , p) = unit-trunc-Prop (x , eq-type-subtype (λ w → fiber (map-emb f) w , is-prop-map-emb f w) p)
```

### The image of a map into a truncated type is truncated

```agda
abstract
  is-trunc-im-emb :
    {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A ↪ X) →
    is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (im-emb f)
  is-trunc-im-emb k f = is-trunc-emb k (emb-im-emb f)

im-emb-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) (X : Truncated-Type l1 (succ-𝕋 k)) {A : UU l2}
  (f : A ↪ type-Truncated-Type X) → Truncated-Type (l1 ⊔ l2) (succ-𝕋 k)
pr1 (im-emb-Truncated-Type k X f) = im-emb f
pr2 (im-emb-Truncated-Type k X f) =
  is-trunc-im-emb k f (is-trunc-type-Truncated-Type X)
```

## Idea

<!-- TODO -->

Consider a map `f : A → B` and a [subtype](foundation-core.subtypes.md) `S ⊆ A`,
then the **image** of `S` under `f` is the subtype of `B` consisting of the
values of the composite `S ⊆ A → B`. In other words, the image `im f S` of a
subtype `S` under `f` satisfies the universal property that

```text
  (im f S ⊆ U) ↔ (S ⊆ U ∘ f).
```

The image operation on subtypes is an
[order preserving map](order-theory.order-preserving-maps-large-posets.md) from
the [powerset](foundation.powersets.md) of `A` to the powerset of `B`. Thus we
obtain a [Galois connection](order-theory.galois-connections-large-posets.md)
between the powersets of `A` and `B`: the **image-pullback Galois connection**

```text
  image-subtype f ⊣ pullback-subtype f.
```

## Definitions

### The predicate of being the image of a subtype under a map

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (S : subtype l3 A)
  where

  is-image-map-subtype : {l4 : Level} (T : subtype l4 B) → UUω
  is-image-map-subtype T =
    {l : Level} (U : subtype l B) → (T ⊆ U) ↔ (S ⊆ U ∘ f)
```

### The image of a subtype under a map

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (S : subtype l3 A)
  where

  im-subtype : subtype (l1 ⊔ l2 ⊔ l3) B
  im-subtype y = subtype-im (f ∘ inclusion-subtype S) y

  is-in-im-subtype : B → UU (l1 ⊔ l2 ⊔ l3)
  is-in-im-subtype = is-in-subtype im-subtype
```

### The order preserving operation taking the image of a subtype under a map

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  preserves-order-im-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 A) →
    S ⊆ T → im-subtype f S ⊆ im-subtype f T
  preserves-order-im-subtype S T H y p =
    apply-universal-property-trunc-Prop p
      ( im-subtype f T y)
      ( λ ((x , s) , q) → unit-trunc-Prop ((x , H x s) , q))

  im-subtype-hom-Large-Poset :
    hom-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( powerset-Large-Poset A)
      ( powerset-Large-Poset B)
  map-hom-Large-Preorder im-subtype-hom-Large-Poset =
    im-subtype f
  preserves-order-hom-Large-Preorder im-subtype-hom-Large-Poset =
    preserves-order-im-subtype
```

### The image-pullback Galois connection on powersets

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  forward-implication-adjoint-relation-image-pullback-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 B) →
    (im-subtype f S ⊆ T) → (S ⊆ pullback-subtype f T)
  forward-implication-adjoint-relation-image-pullback-subtype S T H x p =
    H (f x) (unit-trunc-Prop ((x , p) , refl))

  backward-implication-adjoint-relation-image-pullback-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 B) →
    (S ⊆ pullback-subtype f T) → (im-subtype f S ⊆ T)
  backward-implication-adjoint-relation-image-pullback-subtype S T H y p =
    apply-universal-property-trunc-Prop p
      ( T y)
      ( λ where ((x , s) , refl) → H x s)

  adjoint-relation-image-pullback-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 B) →
    (im-subtype f S ⊆ T) ↔ (S ⊆ pullback-subtype f T)
  pr1 (adjoint-relation-image-pullback-subtype S T) =
    forward-implication-adjoint-relation-image-pullback-subtype S T
  pr2 (adjoint-relation-image-pullback-subtype S T) =
    backward-implication-adjoint-relation-image-pullback-subtype S T

  image-pullback-subtype-galois-connection-Large-Poset :
    galois-connection-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( λ l → l)
      ( powerset-Large-Poset A)
      ( powerset-Large-Poset B)
  lower-adjoint-galois-connection-Large-Poset
    image-pullback-subtype-galois-connection-Large-Poset =
    im-subtype-hom-Large-Poset f
  upper-adjoint-galois-connection-Large-Poset
    image-pullback-subtype-galois-connection-Large-Poset =
    pullback-subtype-hom-Large-Poset f
  adjoint-relation-galois-connection-Large-Poset
    image-pullback-subtype-galois-connection-Large-Poset =
    adjoint-relation-image-pullback-subtype
```

## Properties

### If `S` and `T` have the same elements, then `im-subtype f S` and `im-subtype f T` have the same elements

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (S : subtype l3 A) (T : subtype l4 A)
  where

  has-same-elements-im-has-same-elements-subtype :
    has-same-elements-subtype S T →
    has-same-elements-subtype (im-subtype f S) (im-subtype f T)
  has-same-elements-im-has-same-elements-subtype s =
    has-same-elements-sim-subtype
      ( im-subtype f S)
      ( im-subtype f T)
      ( preserves-sim-hom-Large-Poset
        ( powerset-Large-Poset A)
        ( powerset-Large-Poset B)
        ( im-subtype-hom-Large-Poset f)
        ( S)
        ( T)
        ( sim-has-same-elements-subtype S T s))
```

### The image subtype `im f (full-subtype A)` has the same elements as the subtype `im f`

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  compute-im-full-subtype :
    has-same-elements-subtype
      ( im-subtype f (full-subtype lzero A))
      ( subtype-im f)
  compute-im-full-subtype y =
    iff-equiv
      ( equiv-trunc-Prop
        ( ( right-unit-law-Σ-is-contr
            ( λ a →
              is-contr-map-is-equiv is-equiv-inclusion-full-subtype (pr1 a))) ∘e
          ( compute-fiber-comp f inclusion-full-subtype y)))
```

### The image subtype `im (g ∘ f) S` has the same elements as the image subtype `im g (im f S)`

**Proof:** The asserted similarity follows at once from the similarity

```text
  pullback-subtype (g ∘ f) ≈ pullback-subtype g ∘ pullback-subtype f
```

via the image-pullback Galois connection.

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (S : subtype l4 A)
  where

  compute-im-subtype-comp :
    has-same-elements-subtype
      ( im-subtype (g ∘ f) S)
      ( im-subtype g (im-subtype f S))
  compute-im-subtype-comp =
    has-same-elements-sim-subtype
      ( im-subtype (g ∘ f) S)
      ( im-subtype g (im-subtype f S))
      ( lower-sim-upper-sim-galois-connection-Large-Poset
        ( powerset-Large-Poset A)
        ( powerset-Large-Poset C)
        ( image-pullback-subtype-galois-connection-Large-Poset (g ∘ f))
        ( comp-galois-connection-Large-Poset
          ( powerset-Large-Poset A)
          ( powerset-Large-Poset B)
          ( powerset-Large-Poset C)
          ( image-pullback-subtype-galois-connection-Large-Poset g)
          ( image-pullback-subtype-galois-connection-Large-Poset f))
        ( refl-sim-hom-Large-Poset
          ( powerset-Large-Poset C)
          ( powerset-Large-Poset A)
          ( pullback-subtype-hom-Large-Poset (g ∘ f)))
        ( S))
```

### The image `im (g ∘ f)` has the same elements as the image subtype `im g (im f)`

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C) (f : A → B)
  where

  compute-subtype-im-comp :
    has-same-elements-subtype (subtype-im (g ∘ f)) (im-subtype g (subtype-im f))
  compute-subtype-im-comp x =
    logical-equivalence-reasoning
      is-in-subtype-im (g ∘ f) x
      ↔ is-in-im-subtype (g ∘ f) (full-subtype lzero A) x
        by
        inv-iff (compute-im-full-subtype (g ∘ f) x)
      ↔ is-in-im-subtype g (im-subtype f (full-subtype lzero A)) x
        by
        compute-im-subtype-comp g f (full-subtype lzero A) x
      ↔ is-in-im-subtype g (subtype-im f) x
        by
        has-same-elements-im-has-same-elements-subtype g
          ( im-subtype f (full-subtype lzero A))
          ( subtype-im f)
          ( compute-im-full-subtype f)
          ( x)
```
