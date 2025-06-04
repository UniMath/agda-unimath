# Globularly coskeletal types

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.globularly-coskeletal-types
  {I2 : Level} (I : Nontrivial-Bounded-Total-Order lzero I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.type-arithmetic-booleans
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.retracts-of-types
open import foundation-core.transport-along-identifications
open import foundation-core.truncation-levels

open import simplicial-type-theory.action-on-directed-edges-functions I
open import simplicial-type-theory.dependent-directed-edges I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-edges-cartesian-product-types I
open import simplicial-type-theory.directed-edges-dependent-pair-types I
open import simplicial-type-theory.fully-faithful-maps I
open import simplicial-type-theory.natural-transformations I
open import simplicial-type-theory.simplicially-discrete-types I
open import simplicial-type-theory.whiskering-directed-edges I
```

</details>

## Idea

The globular coskeletality of a type is a measure of the complexity of its
hom-types. The simplest case is a contractible type. This is the base case of
the inductive definition of globular coskeletality for types. A type is
`k+1`-globularly coskeletal if its hom-types are `k`-globularly coskeletal.

**Note.** This is not coskeletality in simplicial spaces, but coskeletality in
globular spaces. However, the two agree in many cases we care about, i.e. when
`k = 0` or the types are Segal.

**Question.** Should `k+1`-globular coskeletality also require the identity
types to be `k`-globular coskeletal? Probably yes, c.f. higher modalities.

## Definition

### The condition of coskeletality

```agda
is-globularly-coskeletal : {l : Level} (k : 𝕋) → UU l → UU l
is-globularly-coskeletal neg-two-𝕋 A = is-contr A
is-globularly-coskeletal (succ-𝕋 k) A =
  (x y : A) → is-globularly-coskeletal k (x →▵ y)

is-globularly-coskeletal-eq :
  {l : Level} {k k' : 𝕋} {A : UU l} →
  k ＝ k' → is-globularly-coskeletal k A → is-globularly-coskeletal k' A
is-globularly-coskeletal-eq refl H = H
```

### The universe of globularly coskeletal types

```agda
Globularly-Coskeletal-Type : (l : Level) → 𝕋 → UU (lsuc l)
Globularly-Coskeletal-Type l k = Σ (UU l) (is-globularly-coskeletal k)

module _
  {k : 𝕋} {l : Level}
  where

  type-Globularly-Coskeletal-Type : Globularly-Coskeletal-Type l k → UU l
  type-Globularly-Coskeletal-Type = pr1

  is-globularly-coskeletal-type-Globularly-Coskeletal-Type :
    (A : Globularly-Coskeletal-Type l k) →
    is-globularly-coskeletal k (type-Globularly-Coskeletal-Type A)
  is-globularly-coskeletal-type-Globularly-Coskeletal-Type = pr2
```

## Properties

### Being globularly coskeletal is a property

```agda
abstract
  is-prop-is-globularly-coskeletal :
    {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-globularly-coskeletal k A)
  is-prop-is-globularly-coskeletal neg-two-𝕋 A = is-property-is-contr
  is-prop-is-globularly-coskeletal (succ-𝕋 k) A =
    is-prop-Π
      ( λ x → is-prop-Π (λ y → is-prop-is-globularly-coskeletal k (x →▵ y)))

is-globularly-coskeletal-Prop : {l : Level} (k : 𝕋) (A : UU l) → Prop l
pr1 (is-globularly-coskeletal-Prop k A) = is-globularly-coskeletal k A
pr2 (is-globularly-coskeletal-Prop k A) = is-prop-is-globularly-coskeletal k A
```

### A type is `-1`-globularly coskeletal if and only if it is `∂Δ¹ ↪ Δ¹`-local

This remains to be formalized.

### A type is `k`-globularly coskeletal if and only if it is local at the `k`'th directed suspension of `0 → 1`

This remains to be formalized.

### If a type is `k`-globularly coskeletal then it is `k+1`-globularly coskeletal

```agda
is-contr-hom-is-contr :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → is-contr (x →▵ y)
is-contr-hom-is-contr H x y =
  is-contr-is-equiv'
    ( x ＝ y)
    ( hom▵-eq)
    ( is-simplicially-discrete-is-contr H x y)
    ( is-prop-is-contr H x y)

abstract
  is-globularly-coskeletal-succ-is-globularly-coskeletal :
    (k : 𝕋) {l : Level} {A : UU l} →
    is-globularly-coskeletal k A → is-globularly-coskeletal (succ-𝕋 k) A
  is-globularly-coskeletal-succ-is-globularly-coskeletal neg-two-𝕋 =
    is-contr-hom-is-contr
  is-globularly-coskeletal-succ-is-globularly-coskeletal (succ-𝕋 k) H x y =
    is-globularly-coskeletal-succ-is-globularly-coskeletal k (H x y)

truncated-type-succ-Globularly-Coskeletal-Type :
  (k : 𝕋) {l : Level} →
  Globularly-Coskeletal-Type l k → Globularly-Coskeletal-Type l (succ-𝕋 k)
pr1 (truncated-type-succ-Globularly-Coskeletal-Type k A) =
  type-Globularly-Coskeletal-Type A
pr2 (truncated-type-succ-Globularly-Coskeletal-Type k A) =
  is-globularly-coskeletal-succ-is-globularly-coskeletal k
    ( is-globularly-coskeletal-type-Globularly-Coskeletal-Type A)
```

### The hom-types of a `k`-globularly coskeletal type are `k`-globularly coskeletal

```agda
abstract
  is-globularly-coskeletal-hom :
    {l : Level} {k : 𝕋} {A : UU l} →
    is-globularly-coskeletal k A →
    (x y : A) → is-globularly-coskeletal k (x →▵ y)
  is-globularly-coskeletal-hom {k = k} =
    is-globularly-coskeletal-succ-is-globularly-coskeletal k

hom-Globularly-Coskeletal-Type :
  {l : Level} {k : 𝕋} (A : Globularly-Coskeletal-Type l (succ-𝕋 k)) →
  (x y : type-Globularly-Coskeletal-Type A) → Globularly-Coskeletal-Type l k
hom-Globularly-Coskeletal-Type A x y =
  ( (x →▵ y) , is-globularly-coskeletal-type-Globularly-Coskeletal-Type A x y)

hom-Globularly-Coskeletal-Type' :
  {l : Level} {k : 𝕋} (A : Globularly-Coskeletal-Type l k) →
  (x y : type-Globularly-Coskeletal-Type A) → Globularly-Coskeletal-Type l k
hom-Globularly-Coskeletal-Type' A x y =
  ( (x →▵ y) ,
    is-globularly-coskeletal-hom
      ( is-globularly-coskeletal-type-Globularly-Coskeletal-Type A) x y)
```

### The identity types of a `k`-globularly coskeletal type are `k`-globularly coskeletal

This should be true for coskeletality to be a modality.

```text
-- abstract
--   is-globularly-coskeletal-Id :
--     {l : Level} {k : 𝕋} {A : UU l} →
--     is-globularly-coskeletal k A → (x y : A) → is-globularly-coskeletal k (x ＝ y)
--   is-globularly-coskeletal-Id {k = neg-two-𝕋} = is-prop-is-contr
--   is-globularly-coskeletal-Id {k = succ-𝕋 k} H x y p q = {!   !}

-- Id-Globularly-Coskeletal-Type' :
--   {l : Level} {k : 𝕋} (A : Globularly-Coskeletal-Type l k) →
--   (x y : type-Globularly-Coskeletal-Type A) → Globularly-Coskeletal-Type l k
-- pr1 (Id-Globularly-Coskeletal-Type' A x y) = (x ＝ y)
-- pr2 (Id-Globularly-Coskeletal-Type' A x y) =
--   is-globularly-coskeletal-Id (is-globularly-coskeletal-type-Globularly-Coskeletal-Type A) x y
```

### `k`-globularly coskeletal types are closed under retracts

```agda
module _
  {l1 l2 : Level}
  where

  is-globularly-coskeletal-retract-of :
    (k : 𝕋) {A : UU l1} {B : UU l2} →
    A retract-of B → is-globularly-coskeletal k B → is-globularly-coskeletal k A
  is-globularly-coskeletal-retract-of neg-two-𝕋 = is-contr-retract-of _
  is-globularly-coskeletal-retract-of (succ-𝕋 k) R H x y =
    is-globularly-coskeletal-retract-of k
      ( retract-hom▵ R x y)
      ( H (pr1 R x) (pr1 R y))
```

### `k`-globularly coskeletal types are closed under equivalences

```agda
abstract
  is-globularly-coskeletal-is-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-globularly-coskeletal k B → is-globularly-coskeletal k A
  is-globularly-coskeletal-is-equiv k B f is-equiv-f =
    is-globularly-coskeletal-retract-of k (f , pr2 is-equiv-f)

abstract
  is-globularly-coskeletal-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-globularly-coskeletal k B → is-globularly-coskeletal k A
  is-globularly-coskeletal-equiv k B (f , is-equiv-f) =
    is-globularly-coskeletal-is-equiv k B f is-equiv-f

abstract
  is-globularly-coskeletal-is-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : UU l1) {B : UU l2} (f : A → B) →
    is-equiv f → is-globularly-coskeletal k A → is-globularly-coskeletal k B
  is-globularly-coskeletal-is-equiv'
    k A f is-equiv-f is-globularly-coskeletal-A =
    is-globularly-coskeletal-is-equiv k A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-globularly-coskeletal-A)

abstract
  is-globularly-coskeletal-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-globularly-coskeletal k A → is-globularly-coskeletal k B
  is-globularly-coskeletal-equiv' k A (f , is-equiv-f) =
    is-globularly-coskeletal-is-equiv' k A f is-equiv-f
```

### If a type simplicially embeds into a `k+1`-globularly coskeletal type, then it is `k+1`-globularly coskeletal

```agda
abstract
  is-globularly-coskeletal-is-simplicially-fully-faithful :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-simplicially-fully-faithful f →
    is-globularly-coskeletal (succ-𝕋 k) B →
    is-globularly-coskeletal (succ-𝕋 k) A
  is-globularly-coskeletal-is-simplicially-fully-faithful k f Ef H x y =
    is-globularly-coskeletal-is-equiv k (f x →▵ f y)
      ( action-hom▵-function f {x} {y})
      ( Ef x y)
      ( H (f x) (f y))

abstract
  is-globularly-coskeletal-simplicially-fully-faithful-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A ↪▵ B) →
    is-globularly-coskeletal (succ-𝕋 k) B →
    is-globularly-coskeletal (succ-𝕋 k) A
  is-globularly-coskeletal-simplicially-fully-faithful-map k f =
    is-globularly-coskeletal-is-simplicially-fully-faithful k
      ( map-simplicially-fully-faithful-map f)
      ( is-simplicially-fully-faithful-map-simplicially-fully-faithful-map f)
```

In fact, it suffices that the action on homs has a retraction.

```agda
abstract
  is-globularly-coskeletal-retraction-ap :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    ((x y : A) → retraction (action-hom▵-function f {x} {y})) →
    is-globularly-coskeletal (succ-𝕋 k) B →
    is-globularly-coskeletal (succ-𝕋 k) A
  is-globularly-coskeletal-retraction-ap k f Ef H x y =
    is-globularly-coskeletal-retract-of k
      ( action-hom▵-function f {x} {y} , Ef x y)
      ( H (f x) (f y))
```

### Globularly coskeletal types are closed under dependent pair types

```text
-- abstract
--   is-globularly-coskeletal-Σ :
--     {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : A → UU l2} →
--     is-globularly-coskeletal k A → ((x : A) → is-globularly-coskeletal k (B x)) → is-globularly-coskeletal k (Σ A B)
--   is-globularly-coskeletal-Σ {k = neg-two-𝕋} is-globularly-coskeletal-A is-globularly-coskeletal-B =
--     is-contr-Σ' is-globularly-coskeletal-A is-globularly-coskeletal-B
--   is-globularly-coskeletal-Σ {k = succ-𝕋 k} {B = B} is-globularly-coskeletal-A is-globularly-coskeletal-B s t =
--     is-globularly-coskeletal-equiv k
--       ( hom▵-Σ s t)
--       ( compute-hom▵-Σ)
--       ( is-globularly-coskeletal-Σ
--         ( is-globularly-coskeletal-A (pr1 s) (pr1 t))
--         {!  is-globularly-coskeletal-B ? ? ? !})

  --   is-globularly-coskeletal-equiv k
  --     ( Σ (pr1 s ＝ pr1 t) (λ p → tr B p (pr2 s) ＝ pr2 t))
  --     ( equiv-pair-eq-Σ s t)
  --     ( is-globularly-coskeletal-Σ
  --       ( is-globularly-coskeletal-A (pr1 s) (pr1 t))
  --       ( λ p → is-globularly-coskeletal-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

-- Σ-Globularly-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Globularly-Coskeletal-Type l1 k)
--   (B : type-Globularly-Coskeletal-Type A → Globularly-Coskeletal-Type l2 k) →
--   Globularly-Coskeletal-Type (l1 ⊔ l2) k
-- pr1 (Σ-Globularly-Coskeletal-Type A B) =
--   Σ (type-Globularly-Coskeletal-Type A) (λ a → type-Globularly-Coskeletal-Type (B a))
-- pr2 (Σ-Globularly-Coskeletal-Type A B) =
--   is-globularly-coskeletal-Σ
--     ( is-globularly-coskeletal-type-Globularly-Coskeletal-Type A)
--     ( λ a → is-globularly-coskeletal-type-Globularly-Coskeletal-Type (B a))

-- fiber-Globularly-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Globularly-Coskeletal-Type l1 k)
--   (B : Globularly-Coskeletal-Type l2 k)
--   (f : type-Globularly-Coskeletal-Type A → type-Globularly-Coskeletal-Type B) →
--   type-Globularly-Coskeletal-Type B → Globularly-Coskeletal-Type (l1 ⊔ l2) k
-- fiber-Globularly-Coskeletal-Type A B f b =
--   Σ-Globularly-Coskeletal-Type A (λ a → Id-Globularly-Coskeletal-Type' B (f a) b)
```

### Products of families of globularly coskeletal types are globularly coskeletal

```agda
abstract
  is-globularly-coskeletal-Π :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-globularly-coskeletal k (B x)) →
    is-globularly-coskeletal k ((x : A) → B x)
  is-globularly-coskeletal-Π neg-two-𝕋 is-globularly-coskeletal-B =
    is-contr-Π is-globularly-coskeletal-B
  is-globularly-coskeletal-Π (succ-𝕋 k) is-globularly-coskeletal-B f g =
    is-globularly-coskeletal-is-equiv k (f ⇒▵ g)
      ( simplicial-natural-transformation-simplicial-edge-of-dependent-functions)
      ( is-equiv-simplicial-natural-transformation-simplicial-edge-of-dependent-functions)
      ( is-globularly-coskeletal-Π k
        ( λ x → is-globularly-coskeletal-B x (f x) (g x)))

type-Π-Globularly-Coskeletal-Type' :
  (k : 𝕋) {l1 l2 : Level}
  (A : UU l1) (B : A → Globularly-Coskeletal-Type l2 k) →
  UU (l1 ⊔ l2)
type-Π-Globularly-Coskeletal-Type' k A B =
  (x : A) → type-Globularly-Coskeletal-Type (B x)

is-globularly-coskeletal-type-Π-Globularly-Coskeletal-Type' :
  (k : 𝕋) {l1 l2 : Level}
  (A : UU l1) (B : A → Globularly-Coskeletal-Type l2 k) →
  is-globularly-coskeletal k (type-Π-Globularly-Coskeletal-Type' k A B)
is-globularly-coskeletal-type-Π-Globularly-Coskeletal-Type' k A B =
  is-globularly-coskeletal-Π k
    ( λ x → is-globularly-coskeletal-type-Globularly-Coskeletal-Type (B x))

Π-Globularly-Coskeletal-Type' :
  (k : 𝕋) {l1 l2 : Level}
  (A : UU l1) (B : A → Globularly-Coskeletal-Type l2 k) →
  Globularly-Coskeletal-Type (l1 ⊔ l2) k
pr1 (Π-Globularly-Coskeletal-Type' k A B) =
  type-Π-Globularly-Coskeletal-Type' k A B
pr2 (Π-Globularly-Coskeletal-Type' k A B) =
  is-globularly-coskeletal-type-Π-Globularly-Coskeletal-Type' k A B

type-Π-Globularly-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Globularly-Coskeletal-Type l1 k)
  (B : type-Globularly-Coskeletal-Type A → Globularly-Coskeletal-Type l2 k) →
  UU (l1 ⊔ l2)
type-Π-Globularly-Coskeletal-Type k A B =
  type-Π-Globularly-Coskeletal-Type' k (type-Globularly-Coskeletal-Type A) B

is-globularly-coskeletal-type-Π-Globularly-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Globularly-Coskeletal-Type l1 k)
  (B : type-Globularly-Coskeletal-Type A → Globularly-Coskeletal-Type l2 k) →
  is-globularly-coskeletal k (type-Π-Globularly-Coskeletal-Type k A B)
is-globularly-coskeletal-type-Π-Globularly-Coskeletal-Type k A B =
  is-globularly-coskeletal-type-Π-Globularly-Coskeletal-Type' k
    ( type-Globularly-Coskeletal-Type A) B

Π-Globularly-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Globularly-Coskeletal-Type l1 k)
  (B : type-Globularly-Coskeletal-Type A → Globularly-Coskeletal-Type l2 k) →
  Globularly-Coskeletal-Type (l1 ⊔ l2) k
Π-Globularly-Coskeletal-Type k A B =
  Π-Globularly-Coskeletal-Type' k (type-Globularly-Coskeletal-Type A) B
```

### The type of functions into a globularly coskeletal type is globularly coskeletal

```agda
abstract
  is-globularly-coskeletal-function-type :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-globularly-coskeletal k B → is-globularly-coskeletal k (A → B)
  is-globularly-coskeletal-function-type k is-globularly-coskeletal-B =
    is-globularly-coskeletal-Π k (λ _ → is-globularly-coskeletal-B)

function-type-Globularly-Coskeletal-Type :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : Globularly-Coskeletal-Type l2 k) →
  Globularly-Coskeletal-Type (l1 ⊔ l2) k
pr1 (function-type-Globularly-Coskeletal-Type A B) =
  A → type-Globularly-Coskeletal-Type B
pr2 (function-type-Globularly-Coskeletal-Type A B) =
  is-globularly-coskeletal-function-type _
    ( is-globularly-coskeletal-type-Globularly-Coskeletal-Type B)

type-function-Globularly-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Globularly-Coskeletal-Type l1 k)
  (B : Globularly-Coskeletal-Type l2 k) → UU (l1 ⊔ l2)
type-function-Globularly-Coskeletal-Type k A B =
  type-Globularly-Coskeletal-Type A → type-Globularly-Coskeletal-Type B

is-globularly-coskeletal-type-function-Globularly-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Globularly-Coskeletal-Type l1 k)
  (B : Globularly-Coskeletal-Type l2 k) →
  is-globularly-coskeletal k (type-function-Globularly-Coskeletal-Type k A B)
is-globularly-coskeletal-type-function-Globularly-Coskeletal-Type k A B =
  is-globularly-coskeletal-function-type k
    ( is-globularly-coskeletal-type-Globularly-Coskeletal-Type B)

function-Globularly-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Globularly-Coskeletal-Type l1 k)
  (B : Globularly-Coskeletal-Type l2 k) → Globularly-Coskeletal-Type (l1 ⊔ l2) k
pr1 (function-Globularly-Coskeletal-Type k A B) =
  type-function-Globularly-Coskeletal-Type k A B
pr2 (function-Globularly-Coskeletal-Type k A B) =
  is-globularly-coskeletal-type-function-Globularly-Coskeletal-Type k A B
```

### Products of globularly coskeletal types are globularly coskeletal

```agda
abstract
  is-globularly-coskeletal-product-Level :
    {l : Level} (k : 𝕋) {A B : UU l} →
    is-globularly-coskeletal k A →
    is-globularly-coskeletal k B →
    is-globularly-coskeletal k (A × B)
  is-globularly-coskeletal-product-Level
    k {A} {B} is-globularly-coskeletal-A is-globularly-coskeletal-B =
    is-globularly-coskeletal-equiv' k
      ( (b : bool) → rec-bool A B b)
      ( equiv-Π-bool-product (rec-bool A B))
      ( is-globularly-coskeletal-Π k
        ( ind-bool
          ( is-globularly-coskeletal k ∘ rec-bool A B)
          ( is-globularly-coskeletal-A)
          ( is-globularly-coskeletal-B)))

abstract
  is-globularly-coskeletal-product :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-globularly-coskeletal k A →
    is-globularly-coskeletal k B →
    is-globularly-coskeletal k (A × B)
  is-globularly-coskeletal-product
    {l1} {l2} k {A} {B} is-globularly-coskeletal-A is-globularly-coskeletal-B =
    is-globularly-coskeletal-equiv k
      ( raise (l1 ⊔ l2) A × raise (l1 ⊔ l2) B)
      ( equiv-product (compute-raise (l1 ⊔ l2) A) (compute-raise (l1 ⊔ l2) B))
      ( is-globularly-coskeletal-product-Level k
        ( is-globularly-coskeletal-equiv' k A
          ( compute-raise (l1 ⊔ l2) A)
          ( is-globularly-coskeletal-A))
        ( is-globularly-coskeletal-equiv' k B
          ( compute-raise (l1 ⊔ l2) B)
          ( is-globularly-coskeletal-B)))

product-Globularly-Coskeletal-Type :
  {l1 l2 : Level} (k : 𝕋) →
  Globularly-Coskeletal-Type l1 k →
  Globularly-Coskeletal-Type l2 k →
  Globularly-Coskeletal-Type (l1 ⊔ l2) k
pr1 (product-Globularly-Coskeletal-Type k A B) =
  type-Globularly-Coskeletal-Type A × type-Globularly-Coskeletal-Type B
pr2 (product-Globularly-Coskeletal-Type k A B) =
  is-globularly-coskeletal-product k
    ( is-globularly-coskeletal-type-Globularly-Coskeletal-Type A)
    ( is-globularly-coskeletal-type-Globularly-Coskeletal-Type B)

is-globularly-coskeletal-product' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-globularly-coskeletal (succ-𝕋 k) A) →
  (A → is-globularly-coskeletal (succ-𝕋 k) B) →
  is-globularly-coskeletal (succ-𝕋 k) (A × B)
is-globularly-coskeletal-product' k f g (a , b) (a' , b') =
  is-globularly-coskeletal-equiv k
    ( hom▵-product (a , b) (a' , b'))
    ( compute-hom▵-product)
    ( is-globularly-coskeletal-product k (f b a a') (g a b b'))

is-globularly-coskeletal-left-factor-product' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-globularly-coskeletal k (A × B) → B → is-globularly-coskeletal k A
is-globularly-coskeletal-left-factor-product' neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-product A B H
is-globularly-coskeletal-left-factor-product' (succ-𝕋 k) H b a a' =
  is-globularly-coskeletal-left-factor-product' k
    ( is-globularly-coskeletal-equiv' k
      ( (a , b) →▵ (a' , b))
      ( compute-hom▵-product)
      ( H (a , b) (a' , b)))
    ( id-hom▵ b)

is-globularly-coskeletal-left-factor-product :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-globularly-coskeletal k (A × B) →
  is-inhabited B →
  is-globularly-coskeletal k A
is-globularly-coskeletal-left-factor-product k {A} {B} H =
  rec-trunc-Prop
    ( is-globularly-coskeletal-Prop k A)
    ( is-globularly-coskeletal-left-factor-product' k H)

is-globularly-coskeletal-right-factor-product' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-globularly-coskeletal k (A × B) → A → is-globularly-coskeletal k B
is-globularly-coskeletal-right-factor-product' neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-product A B H
is-globularly-coskeletal-right-factor-product' (succ-𝕋 k) H a b b' =
  is-globularly-coskeletal-right-factor-product' k
    ( is-globularly-coskeletal-equiv' k
      ( (a , b) →▵ (a , b'))
      ( compute-hom▵-product)
      ( H (a , b) (a , b')))
    ( id-hom▵ a)

is-globularly-coskeletal-right-factor-product :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-globularly-coskeletal k (A × B) →
  is-inhabited A →
  is-globularly-coskeletal k B
is-globularly-coskeletal-right-factor-product k {A} {B} H =
  rec-trunc-Prop
    ( is-globularly-coskeletal-Prop k B)
    ( is-globularly-coskeletal-right-factor-product' k H)
```

### The type of equivalences between globularly coskeletal types is globularly coskeletal

**Proof.** The type of equivalences `A ≃ B` is a pullback

```text
  A ≃ B ---> (B → A) × (A → B) × (B → A)
    | ⌟                   |
    |                     |
    ∨                     ∨
    1 ----------> (A → A) × (B → B)
       (id , id)
```

so the result follows by pullback stability.

```text
-- module _
--   {l1 l2 : Level} {A : UU l1} {B : UU l2}
--   where

--   is-globularly-coskeletal-equiv-is-globularly-coskeletal :
--     (k : 𝕋) → is-globularly-coskeletal k A → is-globularly-coskeletal k B → is-globularly-coskeletal k (A ≃ B)
--   is-globularly-coskeletal-equiv-is-globularly-coskeletal k H K = {!   !}

-- type-equiv-Globularly-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Globularly-Coskeletal-Type l1 k) (B : Globularly-Coskeletal-Type l2 k) →
--   UU (l1 ⊔ l2)
-- type-equiv-Globularly-Coskeletal-Type A B =
--   type-Globularly-Coskeletal-Type A ≃ type-Globularly-Coskeletal-Type B

-- is-globularly-coskeletal-type-equiv-Globularly-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Globularly-Coskeletal-Type l1 k) (B : Globularly-Coskeletal-Type l2 k) →
--   is-globularly-coskeletal k (type-equiv-Globularly-Coskeletal-Type A B)
-- is-globularly-coskeletal-type-equiv-Globularly-Coskeletal-Type A B =
--   is-globularly-coskeletal-equiv-is-globularly-coskeletal _
--     ( is-globularly-coskeletal-type-Globularly-Coskeletal-Type A)
--     ( is-globularly-coskeletal-type-Globularly-Coskeletal-Type B)

-- equiv-Globularly-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Globularly-Coskeletal-Type l1 k) (B : Globularly-Coskeletal-Type l2 k) →
--   Globularly-Coskeletal-Type (l1 ⊔ l2) k
-- pr1 (equiv-Globularly-Coskeletal-Type A B) = type-equiv-Globularly-Coskeletal-Type A B
-- pr2 (equiv-Globularly-Coskeletal-Type A B) = is-globularly-coskeletal-type-equiv-Globularly-Coskeletal-Type A B
```
