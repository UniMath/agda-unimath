# Connected maps

```agda
module foundation.connected-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-extensionality-axiom
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.precomposition-dependent-functions
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.univalence
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-maps
```

</details>

## Idea

A map is said to be **`k`-connected** if its
[fibers](foundation-core.fibers-of-maps.md) are
[`k`-connected types](foundation.connected-types.md).

## Definitions

### Connected maps

```agda
is-connected-map-Prop :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-connected-map-Prop k {B = B} f =
  Π-Prop B (λ b → is-connected-Prop k (fiber f b))

is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-connected-map k f = type-Prop (is-connected-map-Prop k f)

is-prop-is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-connected-map k f)
is-prop-is-connected-map k f = is-prop-type-Prop (is-connected-map-Prop k f)
```

### The type of connected maps between two types

```agda
connected-map : {l1 l2 : Level} (k : 𝕋) → UU l1 → UU l2 → UU (l1 ⊔ l2)
connected-map k A B = type-subtype (is-connected-map-Prop k {A} {B})

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  map-connected-map : connected-map k A B → A → B
  map-connected-map = inclusion-subtype (is-connected-map-Prop k)

  is-connected-map-connected-map :
    (f : connected-map k A B) → is-connected-map k (map-connected-map f)
  is-connected-map-connected-map =
    is-in-subtype-inclusion-subtype (is-connected-map-Prop k)

  emb-inclusion-connected-map : connected-map k A B ↪ (A → B)
  emb-inclusion-connected-map = emb-subtype (is-connected-map-Prop k)

  htpy-connected-map : (f g : connected-map k A B) → UU (l1 ⊔ l2)
  htpy-connected-map f g = (map-connected-map f) ~ (map-connected-map g)

  refl-htpy-connected-map : (f : connected-map k A B) → htpy-connected-map f f
  refl-htpy-connected-map f = refl-htpy

  is-torsorial-htpy-connected-map :
    (f : connected-map k A B) → is-torsorial (htpy-connected-map f)
  is-torsorial-htpy-connected-map f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-connected-map f))
      ( is-prop-is-connected-map k)
      ( map-connected-map f)
      ( refl-htpy-connected-map f)
      ( is-connected-map-connected-map f)

  htpy-eq-connected-map :
    (f g : connected-map k A B) → f ＝ g → htpy-connected-map f g
  htpy-eq-connected-map f .f refl = refl-htpy-connected-map f

  is-equiv-htpy-eq-connected-map :
    (f g : connected-map k A B) → is-equiv (htpy-eq-connected-map f g)
  is-equiv-htpy-eq-connected-map f =
    fundamental-theorem-id
      ( is-torsorial-htpy-connected-map f)
      ( htpy-eq-connected-map f)

  extensionality-connected-map :
    (f g : connected-map k A B) → (f ＝ g) ≃ htpy-connected-map f g
  pr1 (extensionality-connected-map f g) = htpy-eq-connected-map f g
  pr2 (extensionality-connected-map f g) = is-equiv-htpy-eq-connected-map f g

  eq-htpy-connected-map :
    (f g : connected-map k A B) → htpy-connected-map f g → (f ＝ g)
  eq-htpy-connected-map f g =
    map-inv-equiv (extensionality-connected-map f g)
```

### The type of connected maps into a type

```agda
Connected-Map :
  {l1 : Level} (l2 : Level) (k : 𝕋) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Connected-Map l2 k A = Σ (UU l2) (λ X → connected-map k A X)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (f : Connected-Map l2 k A)
  where

  type-Connected-Map : UU l2
  type-Connected-Map = pr1 f

  connected-map-Connected-Map : connected-map k A type-Connected-Map
  connected-map-Connected-Map = pr2 f

  map-Connected-Map : A → type-Connected-Map
  map-Connected-Map = map-connected-map connected-map-Connected-Map

  is-connected-map-Connected-Map : is-connected-map k map-Connected-Map
  is-connected-map-Connected-Map =
    is-connected-map-connected-map connected-map-Connected-Map
```

### The type of connected maps into a truncated type

```agda
Connected-Map-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k l : 𝕋) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Connected-Map-Into-Truncated-Type l2 k l A =
  Σ (Truncated-Type l2 l) (λ X → connected-map k A (type-Truncated-Type X))

module _
  {l1 l2 : Level} {k l : 𝕋} {A : UU l1}
  (f : Connected-Map-Into-Truncated-Type l2 k l A)
  where

  truncated-type-Connected-Map-Into-Truncated-Type : Truncated-Type l2 l
  truncated-type-Connected-Map-Into-Truncated-Type = pr1 f

  type-Connected-Map-Into-Truncated-Type : UU l2
  type-Connected-Map-Into-Truncated-Type =
    type-Truncated-Type truncated-type-Connected-Map-Into-Truncated-Type

  is-trunc-type-Connected-Map-Into-Truncated-Type :
    is-trunc l type-Connected-Map-Into-Truncated-Type
  is-trunc-type-Connected-Map-Into-Truncated-Type =
    is-trunc-type-Truncated-Type
      truncated-type-Connected-Map-Into-Truncated-Type

  connected-map-Connected-Map-Into-Truncated-Type :
    connected-map k A type-Connected-Map-Into-Truncated-Type
  connected-map-Connected-Map-Into-Truncated-Type = pr2 f

  map-Connected-Map-Into-Truncated-Type :
    A → type-Connected-Map-Into-Truncated-Type
  map-Connected-Map-Into-Truncated-Type =
    map-connected-map connected-map-Connected-Map-Into-Truncated-Type

  is-connected-map-Connected-Map-Into-Truncated-Type :
    is-connected-map k map-Connected-Map-Into-Truncated-Type
  is-connected-map-Connected-Map-Into-Truncated-Type =
    is-connected-map-connected-map
      connected-map-Connected-Map-Into-Truncated-Type
```

## Properties

### All maps are `(-2)`-connected

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-neg-two-connected-map : is-connected-map neg-two-𝕋 f
  is-neg-two-connected-map b = is-neg-two-connected (fiber f b)
```

### Equivalences are `k`-connected for any `k`

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-map-is-equiv :
    {f : A → B} → is-equiv f → is-connected-map k f
  is-connected-map-is-equiv H b =
    is-connected-is-contr k (is-contr-map-is-equiv H b)

  is-connected-map-equiv :
    (e : A ≃ B) → is-connected-map k (map-equiv e)
  is-connected-map-equiv e =
    is-connected-map-is-equiv (is-equiv-map-equiv e)

  connected-map-equiv :
    (A ≃ B) → connected-map k A B
  pr1 (connected-map-equiv e) = map-equiv e
  pr2 (connected-map-equiv e) = is-connected-map-equiv e
```

### A `(k+1)`-connected map is `k`-connected

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-connected-map-is-connected-map-succ-𝕋 :
    is-connected-map (succ-𝕋 k) f → is-connected-map k f
  is-connected-map-is-connected-map-succ-𝕋 H b =
    is-connected-is-connected-succ-𝕋 k (H b)
```

### The composition of two `k`-connected maps is `k`-connected

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-connected-map-comp :
    {g : B → C} {f : A → B} →
    is-connected-map k g → is-connected-map k f → is-connected-map k (g ∘ f)
  is-connected-map-comp K H c =
    is-connected-equiv
      ( compute-fiber-comp _ _ c)
      ( is-connected-Σ k (K c) (H ∘ pr1))

  comp-connected-map :
    connected-map k B C → connected-map k A B → connected-map k A C
  pr1 (comp-connected-map g f) =
    map-connected-map g ∘ map-connected-map f
  pr2 (comp-connected-map g f) =
    is-connected-map-comp
      ( is-connected-map-connected-map g)
      ( is-connected-map-connected-map f)
```

### The total map induced by a family of maps is `k`-connected if and only if all maps in the family are `k`-connected

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  is-connected-map-tot-is-fiberwise-connected-map :
    ((x : A) → is-connected-map k (f x)) →
    is-connected-map k (tot f)
  is-connected-map-tot-is-fiberwise-connected-map H (x , y) =
    is-connected-equiv (compute-fiber-tot f (x , y)) (H x y)

  is-fiberwise-connected-map-is-connected-map-tot :
    is-connected-map k (tot f) →
    (x : A) → is-connected-map k (f x)
  is-fiberwise-connected-map-is-connected-map-tot H x y =
    is-connected-equiv (inv-compute-fiber-tot f (x , y)) (H (x , y))
```

### Dependent universal property for connected maps

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  dependent-universal-property-connected-map : UUω
  dependent-universal-property-connected-map =
    {l3 : Level} (P : B → Truncated-Type l3 k) →
    is-equiv (precomp-Π f (λ b → type-Truncated-Type (P b)))

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B}
  where

  dependent-universal-property-is-connected-map :
    is-connected-map k f → dependent-universal-property-connected-map k f
  dependent-universal-property-is-connected-map H P =
    is-equiv-precomp-Π-fiber-condition
      ( λ b → is-equiv-diagonal-exponential-is-connected (P b) (H b))

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : connected-map k A B)
  where

  equiv-dependent-universal-property-is-connected-map :
    {l3 : Level} (P : B → Truncated-Type l3 k) →
    ((b : B) → type-Truncated-Type (P b)) ≃
    ((a : A) → type-Truncated-Type (P (map-connected-map f a)))
  pr1 (equiv-dependent-universal-property-is-connected-map P) =
    precomp-Π (map-connected-map f) (λ b → type-Truncated-Type (P b))
  pr2 (equiv-dependent-universal-property-is-connected-map P) =
    dependent-universal-property-is-connected-map k
      ( is-connected-map-connected-map f)
      ( P)
```

### A map that satisfies the dependent universal property for connected maps is a connected map

**Proof:** Consider a map `f : A → B` such that the precomposition function

```text
  - ∘ f : ((b : B) → P b) → ((a : A) → P (f a))
```

is an equivalence for every family `P` of `k`-truncated types. Then it follows
that the precomposition function

```text
  - ∘ f : ((b : B) → ║fiber f b║ₖ) → ((a : A) → ║fiber f (f a)║ₖ)
```

is an equivalence. In particular, the element `λ a → η (a , refl)` in the
codomain of this equivalence induces an element `c b : ║fiber f b║ₖ` for each
`b : B`. We take these elements as our centers of contraction. Note that by
construction, we have an identification `c (f a) ＝ η (a , refl)`.

To construct a contraction of `║fiber f b║ₖ` for each `b : B`, we have to show
that

```text
  (b : B) (u : ║fiber f b║ₖ) → c b ＝ u.
```

Since the type `c b ＝ u` is `k`-truncated, this type is equivalent to the type
`(b : B) (u : fiber f b) → c b ＝ η u`. By reduction of the universal
quantification over the fibers we see that this type is equivalent to the type

```text
  (a : A) → c (f a) ＝ η (a , refl).
```

This identification holds by construction of `c`.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B}
  (H : dependent-universal-property-connected-map k f)
  where

  center-is-connected-map-dependent-universal-property-connected-map :
    (b : B) → type-trunc k (fiber f b)
  center-is-connected-map-dependent-universal-property-connected-map =
    map-inv-is-equiv
      ( H (λ b → trunc k (fiber f b)))
      ( λ a → unit-trunc (a , refl))

  compute-center-is-connected-map-dependent-universal-property-connected-map :
    (a : A) →
    center-is-connected-map-dependent-universal-property-connected-map (f a) ＝
    unit-trunc (a , refl)
  compute-center-is-connected-map-dependent-universal-property-connected-map =
    htpy-eq
      ( is-section-map-inv-is-equiv
        ( H (λ b → trunc k (fiber f b)))
        ( λ a → unit-trunc (a , refl)))

  contraction-is-connected-map-dependent-universal-property-connected-map :
    (b : B) (u : type-trunc k (fiber f b)) →
    center-is-connected-map-dependent-universal-property-connected-map b ＝ u
  contraction-is-connected-map-dependent-universal-property-connected-map =
    map-Π
      ( λ b →
        function-dependent-universal-property-trunc
          ( Id-Truncated-Type' (trunc k (fiber f b)) _))
      ( extend-lift-family-of-elements-fiber f
        ( λ b u → _ ＝ unit-trunc u)
        ( compute-center-is-connected-map-dependent-universal-property-connected-map))

  abstract
    is-connected-map-dependent-universal-property-connected-map :
      is-connected-map k f
    pr1 (is-connected-map-dependent-universal-property-connected-map b) =
      center-is-connected-map-dependent-universal-property-connected-map b
    pr2 (is-connected-map-dependent-universal-property-connected-map b) =
      contraction-is-connected-map-dependent-universal-property-connected-map b
```

### The map `unit-trunc {k}` is `k`-connected

```agda
module _
  {l1 : Level} (k : 𝕋) {A : UU l1}
  where

  is-connected-map-unit-trunc :
    is-connected-map k (unit-trunc {k = k} {A = A})
  is-connected-map-unit-trunc =
    is-connected-map-dependent-universal-property-connected-map k
      dependent-universal-property-trunc
```

### A map `f : A → B` is `k`-connected if and only if precomposing dependent functions into `k + n`-truncated types is an `n-2`-truncated map for all `n : ℕ`

```agda
is-trunc-map-precomp-Π-is-connected-map :
  {l1 l2 l3 : Level} (k l n : 𝕋) → k +𝕋 (succ-𝕋 (succ-𝕋 n)) ＝ l →
  {A : UU l1} {B : UU l2} {f : A → B} → is-connected-map k f →
  (P : B → Truncated-Type l3 l) →
  is-trunc-map
    ( n)
    ( precomp-Π f (λ b → type-Truncated-Type (P b)))
is-trunc-map-precomp-Π-is-connected-map
  {l1} {l2} {l3} k ._ neg-two-𝕋 refl {A} {B} H P =
  is-contr-map-is-equiv
    ( dependent-universal-property-is-connected-map k H
      ( λ b →
        pair
          ( type-Truncated-Type (P b))
          ( is-trunc-eq
            ( right-unit-law-add-𝕋 k)
            ( is-trunc-type-Truncated-Type (P b)))))
is-trunc-map-precomp-Π-is-connected-map k ._ (succ-𝕋 n) refl {A} {B} {f} H P =
  is-trunc-map-succ-precomp-Π
    ( λ g h →
      is-trunc-map-precomp-Π-is-connected-map k _ n refl H
        ( λ b →
          pair
            ( eq-value g h b)
            ( is-trunc-eq
              ( right-successor-law-add-𝕋 k n)
              ( is-trunc-type-Truncated-Type (P b))
              ( g b)
              ( h b))))
```

### Characterization of the identity type of `Connected-Map l2 k A`

```agda
equiv-Connected-Map :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  (f g : Connected-Map l2 k A) → UU (l1 ⊔ l2)
equiv-Connected-Map f g =
  Σ ( type-Connected-Map f ≃ type-Connected-Map g)
    ( λ e → (map-equiv e ∘ map-Connected-Map f) ~ map-Connected-Map g)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (f : Connected-Map l2 k A)
  where

  id-equiv-Connected-Map : equiv-Connected-Map f f
  pr1 id-equiv-Connected-Map = id-equiv
  pr2 id-equiv-Connected-Map = refl-htpy

  is-torsorial-equiv-Connected-Map :
    is-torsorial (equiv-Connected-Map f)
  is-torsorial-equiv-Connected-Map =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Connected-Map f))
      ( pair (type-Connected-Map f) id-equiv)
      ( is-torsorial-htpy-connected-map (connected-map-Connected-Map f))

  equiv-eq-Connected-Map :
    (g : Connected-Map l2 k A) → (f ＝ g) → equiv-Connected-Map f g
  equiv-eq-Connected-Map .f refl = id-equiv-Connected-Map

  is-equiv-equiv-eq-Connected-Map :
    (g : Connected-Map l2 k A) → is-equiv (equiv-eq-Connected-Map g)
  is-equiv-equiv-eq-Connected-Map =
    fundamental-theorem-id
      is-torsorial-equiv-Connected-Map
      equiv-eq-Connected-Map

  extensionality-Connected-Map :
    (g : Connected-Map l2 k A) → (f ＝ g) ≃ equiv-Connected-Map f g
  pr1 (extensionality-Connected-Map g) = equiv-eq-Connected-Map g
  pr2 (extensionality-Connected-Map g) = is-equiv-equiv-eq-Connected-Map g

  eq-equiv-Connected-Map :
    (g : Connected-Map l2 k A) → equiv-Connected-Map f g → (f ＝ g)
  eq-equiv-Connected-Map g =
    map-inv-equiv (extensionality-Connected-Map g)
```

### Characterization of the identity type of `Connected-Map-Into-Truncated-Type l2 k A`

```agda
equiv-Connected-Map-Into-Truncated-Type :
  {l1 l2 : Level} {k l : 𝕋} {A : UU l1} →
  (f g : Connected-Map-Into-Truncated-Type l2 k l A) → UU (l1 ⊔ l2)
equiv-Connected-Map-Into-Truncated-Type f g =
  Σ ( type-Connected-Map-Into-Truncated-Type f ≃
      type-Connected-Map-Into-Truncated-Type g)
    ( λ e →
      ( map-equiv e ∘ map-Connected-Map-Into-Truncated-Type f) ~
      ( map-Connected-Map-Into-Truncated-Type g))

module _
  {l1 l2 : Level} {k l : 𝕋} {A : UU l1}
  (f : Connected-Map-Into-Truncated-Type l2 k l A)
  where

  id-equiv-Connected-Map-Into-Truncated-Type :
    equiv-Connected-Map-Into-Truncated-Type f f
  pr1 id-equiv-Connected-Map-Into-Truncated-Type = id-equiv
  pr2 id-equiv-Connected-Map-Into-Truncated-Type = refl-htpy

  is-torsorial-equiv-Connected-Map-Into-Truncated-Type :
    is-torsorial (equiv-Connected-Map-Into-Truncated-Type f)
  is-torsorial-equiv-Connected-Map-Into-Truncated-Type =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-Truncated-Type
        ( truncated-type-Connected-Map-Into-Truncated-Type f))
      ( pair (truncated-type-Connected-Map-Into-Truncated-Type f) id-equiv)
      ( is-torsorial-htpy-connected-map
        ( connected-map-Connected-Map-Into-Truncated-Type f))

  equiv-eq-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
    (f ＝ g) → equiv-Connected-Map-Into-Truncated-Type f g
  equiv-eq-Connected-Map-Into-Truncated-Type .f refl =
    id-equiv-Connected-Map-Into-Truncated-Type

  is-equiv-equiv-eq-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
    is-equiv (equiv-eq-Connected-Map-Into-Truncated-Type g)
  is-equiv-equiv-eq-Connected-Map-Into-Truncated-Type =
    fundamental-theorem-id
      is-torsorial-equiv-Connected-Map-Into-Truncated-Type
      equiv-eq-Connected-Map-Into-Truncated-Type

  extensionality-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
    (f ＝ g) ≃ equiv-Connected-Map-Into-Truncated-Type f g
  pr1 (extensionality-Connected-Map-Into-Truncated-Type g) =
    equiv-eq-Connected-Map-Into-Truncated-Type g
  pr2 (extensionality-Connected-Map-Into-Truncated-Type g) =
    is-equiv-equiv-eq-Connected-Map-Into-Truncated-Type g

  eq-equiv-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
      equiv-Connected-Map-Into-Truncated-Type f g → (f ＝ g)
  eq-equiv-Connected-Map-Into-Truncated-Type g =
    map-inv-equiv (extensionality-Connected-Map-Into-Truncated-Type g)
```

### The type `Connected-Map-Into-Truncated-Type l2 k k A` is contractible

This remains to be shown.
[#733](https://github.com/UniMath/agda-unimath/issues/733)

### The type `Connected-Map-Into-Truncated-Type l2 k l A` is `k - l - 2`-truncated

This remains to be shown.
[#733](https://github.com/UniMath/agda-unimath/issues/733)
