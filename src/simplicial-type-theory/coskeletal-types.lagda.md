# Coskeletal types

```agda
module simplicial-type-theory.coskeletal-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
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

open import simplicial-type-theory.action-on-directed-edges-functions
open import simplicial-type-theory.dependent-simplicial-edges
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-edges-cartesian-product-types
open import simplicial-type-theory.directed-edges-dependent-pair-types
open import simplicial-type-theory.simplicial-natural-transformations
open import simplicial-type-theory.simplicially-discrete-types
open import simplicial-type-theory.simplicially-fully-faithful-maps
open import simplicial-type-theory.whiskering-directed-edges
```

</details>

## Idea

The coskeletality of a type is a measure of the complexity of its hom-types. The
simplest case is a contractible type. This is the base case of the inductive
definition of coskeletality for types. A type is `k+1`-coskeletal if its
hom-types are `k`-coskeletal.

**Note.** This is not coskeletality in simplicial spaces, but coskeletality in
globular spaces. However, the two mostly agree in the cases we care about, i.e.
when `k = 0` or the types are Segal.

**Question.** Should `k+1`-coskeletality also require the identity types to be
`k`-coskeletal? Probably yes, c.f. higher modalities.

## Definition

### The condition of coskeletality

```agda
is-coskeletal : {l : Level} (k : 𝕋) → UU l → UU l
is-coskeletal neg-two-𝕋 A = is-contr A
is-coskeletal (succ-𝕋 k) A = (x y : A) → is-coskeletal k (x →₂ y)

is-coskeletal-eq :
  {l : Level} {k k' : 𝕋} {A : UU l} →
  k ＝ k' → is-coskeletal k A → is-coskeletal k' A
is-coskeletal-eq refl H = H
```

### The universe of coskeletal types

```agda
Coskeletal-Type : (l : Level) → 𝕋 → UU (lsuc l)
Coskeletal-Type l k = Σ (UU l) (is-coskeletal k)

module _
  {k : 𝕋} {l : Level}
  where

  type-Coskeletal-Type : Coskeletal-Type l k → UU l
  type-Coskeletal-Type = pr1

  is-coskeletal-type-Coskeletal-Type :
    (A : Coskeletal-Type l k) → is-coskeletal k (type-Coskeletal-Type A)
  is-coskeletal-type-Coskeletal-Type = pr2
```

## Properties

### Being coskeletal is a property

```agda
abstract
  is-prop-is-coskeletal :
    {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-coskeletal k A)
  is-prop-is-coskeletal neg-two-𝕋 A = is-property-is-contr
  is-prop-is-coskeletal (succ-𝕋 k) A =
    is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-coskeletal k (x →₂ y)))

is-coskeletal-Prop : {l : Level} (k : 𝕋) (A : UU l) → Prop l
pr1 (is-coskeletal-Prop k A) = is-coskeletal k A
pr2 (is-coskeletal-Prop k A) = is-prop-is-coskeletal k A
```

### A type is `-1`-coskeletal if and only if it is `∂𝟚 ↪ 𝟚`-local

This remains to be formalized.

### A type is `k`-coskeletal if and only if it is local at the `k`'th directed suspension of `0 → 1`

This remains to be formalized.

### If a type is `k`-coskeletal then it is `k+1`-coskeletal

```agda
is-contr-hom-is-contr :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → is-contr (x →₂ y)
is-contr-hom-is-contr H x y =
  is-contr-is-equiv'
    ( x ＝ y)
    ( simplicial-hom-eq)
    ( is-simplicially-discrete-is-contr H x y)
    ( is-prop-is-contr H x y)

abstract
  is-coskeletal-succ-is-coskeletal :
    (k : 𝕋) {l : Level} {A : UU l} →
    is-coskeletal k A → is-coskeletal (succ-𝕋 k) A
  is-coskeletal-succ-is-coskeletal neg-two-𝕋 = is-contr-hom-is-contr
  is-coskeletal-succ-is-coskeletal (succ-𝕋 k) H x y =
    is-coskeletal-succ-is-coskeletal k (H x y)

truncated-type-succ-Coskeletal-Type :
  (k : 𝕋) {l : Level} → Coskeletal-Type l k → Coskeletal-Type l (succ-𝕋 k)
pr1 (truncated-type-succ-Coskeletal-Type k A) = type-Coskeletal-Type A
pr2 (truncated-type-succ-Coskeletal-Type k A) =
  is-coskeletal-succ-is-coskeletal k (is-coskeletal-type-Coskeletal-Type A)
```

### The hom-types of a `k`-coskeletal type are `k`-coskeletal

```agda
abstract
  is-coskeletal-hom :
    {l : Level} {k : 𝕋} {A : UU l} →
    is-coskeletal k A → (x y : A) → is-coskeletal k (x →₂ y)
  is-coskeletal-hom {k = k} = is-coskeletal-succ-is-coskeletal k

hom-Coskeletal-Type :
  {l : Level} {k : 𝕋} (A : Coskeletal-Type l (succ-𝕋 k)) →
  (x y : type-Coskeletal-Type A) → Coskeletal-Type l k
hom-Coskeletal-Type A x y =
  ( (x →₂ y) , is-coskeletal-type-Coskeletal-Type A x y)

hom-Coskeletal-Type' :
  {l : Level} {k : 𝕋} (A : Coskeletal-Type l k) →
  (x y : type-Coskeletal-Type A) → Coskeletal-Type l k
hom-Coskeletal-Type' A x y =
  ( (x →₂ y) , is-coskeletal-hom (is-coskeletal-type-Coskeletal-Type A) x y)
```

### The identity types of a `k`-coskeletal type are `k`-coskeletal

```agda
-- abstract
--   is-coskeletal-Id :
--     {l : Level} {k : 𝕋} {A : UU l} →
--     is-coskeletal k A → (x y : A) → is-coskeletal k (x ＝ y)
--   is-coskeletal-Id {k = neg-two-𝕋} = is-prop-is-contr
--   is-coskeletal-Id {k = succ-𝕋 k} H x y p q = {!   !}

-- Id-Coskeletal-Type' :
--   {l : Level} {k : 𝕋} (A : Coskeletal-Type l k) →
--   (x y : type-Coskeletal-Type A) → Coskeletal-Type l k
-- pr1 (Id-Coskeletal-Type' A x y) = (x ＝ y)
-- pr2 (Id-Coskeletal-Type' A x y) =
--   is-coskeletal-Id (is-coskeletal-type-Coskeletal-Type A) x y
```

### `k`-coskeletal types are closed under retracts

```agda
module _
  {l1 l2 : Level}
  where

  is-coskeletal-retract-of :
    (k : 𝕋) {A : UU l1} {B : UU l2} →
    A retract-of B → is-coskeletal k B → is-coskeletal k A
  is-coskeletal-retract-of neg-two-𝕋 = is-contr-retract-of _
  is-coskeletal-retract-of (succ-𝕋 k) R H x y =
    is-coskeletal-retract-of k
      ( retract-simplicial-hom R x y)
      ( H (pr1 R x) (pr1 R y))
```

### `k`-coskeletal types are closed under equivalences

```agda
abstract
  is-coskeletal-is-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-coskeletal k B → is-coskeletal k A
  is-coskeletal-is-equiv k B f is-equiv-f =
    is-coskeletal-retract-of k (f , pr2 is-equiv-f)

abstract
  is-coskeletal-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-coskeletal k B → is-coskeletal k A
  is-coskeletal-equiv k B (f , is-equiv-f) =
    is-coskeletal-is-equiv k B f is-equiv-f

abstract
  is-coskeletal-is-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : UU l1) {B : UU l2} (f : A → B) →
    is-equiv f → is-coskeletal k A → is-coskeletal k B
  is-coskeletal-is-equiv' k A f is-equiv-f is-coskeletal-A =
    is-coskeletal-is-equiv k A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-coskeletal-A)

abstract
  is-coskeletal-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-coskeletal k A → is-coskeletal k B
  is-coskeletal-equiv' k A (f , is-equiv-f) =
    is-coskeletal-is-equiv' k A f is-equiv-f
```

### If a type simplicially embeds into a `k+1`-coskeletal type, then it is `k+1`-coskeletal

```agda
abstract
  is-coskeletal-is-simplicially-fully-faithful :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-simplicially-fully-faithful f →
    is-coskeletal (succ-𝕋 k) B →
    is-coskeletal (succ-𝕋 k) A
  is-coskeletal-is-simplicially-fully-faithful k f Ef H x y =
    is-coskeletal-is-equiv k (f x →₂ f y)
      ( action-simplicial-hom-function f {x} {y})
      ( Ef x y)
      ( H (f x) (f y))

abstract
  is-coskeletal-simplicially-fully-faithful-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A ↪▵ B) →
    is-coskeletal (succ-𝕋 k) B → is-coskeletal (succ-𝕋 k) A
  is-coskeletal-simplicially-fully-faithful-map k f =
    is-coskeletal-is-simplicially-fully-faithful k
      ( map-simplicially-fully-faithful-map f)
      ( is-simplicially-fully-faithful-map-simplicially-fully-faithful-map f)
```

In fact, it suffices that the action on homs has a retraction.

```agda
abstract
  is-coskeletal-retraction-ap :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    ((x y : A) → retraction (action-simplicial-hom-function f {x} {y})) →
    is-coskeletal (succ-𝕋 k) B →
    is-coskeletal (succ-𝕋 k) A
  is-coskeletal-retraction-ap k f Ef H x y =
    is-coskeletal-retract-of k
      ( action-simplicial-hom-function f {x} {y} , Ef x y)
      ( H (f x) (f y))
```

### Coskeletal types are closed under dependent pair types

```agda
-- abstract
--   is-coskeletal-Σ :
--     {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : A → UU l2} →
--     is-coskeletal k A → ((x : A) → is-coskeletal k (B x)) → is-coskeletal k (Σ A B)
--   is-coskeletal-Σ {k = neg-two-𝕋} is-coskeletal-A is-coskeletal-B =
--     is-contr-Σ' is-coskeletal-A is-coskeletal-B
--   is-coskeletal-Σ {k = succ-𝕋 k} {B = B} is-coskeletal-A is-coskeletal-B s t =
--     is-coskeletal-equiv k
--       ( simplicial-hom-Σ s t)
--       ( compute-simplicial-hom-Σ)
--       ( is-coskeletal-Σ
--         ( is-coskeletal-A (pr1 s) (pr1 t))
--         {!  is-coskeletal-B ? ? ? !})

  --   is-coskeletal-equiv k
  --     ( Σ (pr1 s ＝ pr1 t) (λ p → tr B p (pr2 s) ＝ pr2 t))
  --     ( equiv-pair-eq-Σ s t)
  --     ( is-coskeletal-Σ
  --       ( is-coskeletal-A (pr1 s) (pr1 t))
  --       ( λ p → is-coskeletal-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

-- Σ-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Coskeletal-Type l1 k)
--   (B : type-Coskeletal-Type A → Coskeletal-Type l2 k) →
--   Coskeletal-Type (l1 ⊔ l2) k
-- pr1 (Σ-Coskeletal-Type A B) =
--   Σ (type-Coskeletal-Type A) (λ a → type-Coskeletal-Type (B a))
-- pr2 (Σ-Coskeletal-Type A B) =
--   is-coskeletal-Σ
--     ( is-coskeletal-type-Coskeletal-Type A)
--     ( λ a → is-coskeletal-type-Coskeletal-Type (B a))

-- fiber-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Coskeletal-Type l1 k)
--   (B : Coskeletal-Type l2 k)
--   (f : type-Coskeletal-Type A → type-Coskeletal-Type B) →
--   type-Coskeletal-Type B → Coskeletal-Type (l1 ⊔ l2) k
-- fiber-Coskeletal-Type A B f b =
--   Σ-Coskeletal-Type A (λ a → Id-Coskeletal-Type' B (f a) b)
```

### Products of families of coskeletal types are coskeletal

```agda
abstract
  is-coskeletal-Π :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-coskeletal k (B x)) → is-coskeletal k ((x : A) → B x)
  is-coskeletal-Π neg-two-𝕋 is-coskeletal-B = is-contr-Π is-coskeletal-B
  is-coskeletal-Π (succ-𝕋 k) is-coskeletal-B f g =
    is-coskeletal-is-equiv k (f ⇒₂ g)
      ( simplicial-natural-transformation-simplicial-edge-of-dependent-functions)
      ( is-equiv-simplicial-natural-transformation-simplicial-edge-of-dependent-functions)
      ( is-coskeletal-Π k (λ x → is-coskeletal-B x (f x) (g x)))

type-Π-Coskeletal-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → Coskeletal-Type l2 k) →
  UU (l1 ⊔ l2)
type-Π-Coskeletal-Type' k A B = (x : A) → type-Coskeletal-Type (B x)

is-coskeletal-type-Π-Coskeletal-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → Coskeletal-Type l2 k) →
  is-coskeletal k (type-Π-Coskeletal-Type' k A B)
is-coskeletal-type-Π-Coskeletal-Type' k A B =
  is-coskeletal-Π k (λ x → is-coskeletal-type-Coskeletal-Type (B x))

Π-Coskeletal-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → Coskeletal-Type l2 k) →
  Coskeletal-Type (l1 ⊔ l2) k
pr1 (Π-Coskeletal-Type' k A B) = type-Π-Coskeletal-Type' k A B
pr2 (Π-Coskeletal-Type' k A B) = is-coskeletal-type-Π-Coskeletal-Type' k A B

type-Π-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Coskeletal-Type l1 k)
  (B : type-Coskeletal-Type A → Coskeletal-Type l2 k) →
  UU (l1 ⊔ l2)
type-Π-Coskeletal-Type k A B =
  type-Π-Coskeletal-Type' k (type-Coskeletal-Type A) B

is-coskeletal-type-Π-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Coskeletal-Type l1 k)
  (B : type-Coskeletal-Type A → Coskeletal-Type l2 k) →
  is-coskeletal k (type-Π-Coskeletal-Type k A B)
is-coskeletal-type-Π-Coskeletal-Type k A B =
  is-coskeletal-type-Π-Coskeletal-Type' k (type-Coskeletal-Type A) B

Π-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Coskeletal-Type l1 k)
  (B : type-Coskeletal-Type A → Coskeletal-Type l2 k) →
  Coskeletal-Type (l1 ⊔ l2) k
Π-Coskeletal-Type k A B =
  Π-Coskeletal-Type' k (type-Coskeletal-Type A) B
```

### The type of functions into a truncated type is truncated

```agda
abstract
  is-coskeletal-function-type :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-coskeletal k B → is-coskeletal k (A → B)
  is-coskeletal-function-type k {A} {B} is-coskeletal-B =
    is-coskeletal-Π k {B = λ (x : A) → B} (λ _ → is-coskeletal-B)

function-type-Coskeletal-Type :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : Coskeletal-Type l2 k) →
  Coskeletal-Type (l1 ⊔ l2) k
pr1 (function-type-Coskeletal-Type A B) = A → type-Coskeletal-Type B
pr2 (function-type-Coskeletal-Type A B) =
  is-coskeletal-function-type _ (is-coskeletal-type-Coskeletal-Type B)

type-function-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Coskeletal-Type l1 k)
  (B : Coskeletal-Type l2 k) → UU (l1 ⊔ l2)
type-function-Coskeletal-Type k A B =
  type-Coskeletal-Type A → type-Coskeletal-Type B

is-coskeletal-type-function-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Coskeletal-Type l1 k)
  (B : Coskeletal-Type l2 k) →
  is-coskeletal k (type-function-Coskeletal-Type k A B)
is-coskeletal-type-function-Coskeletal-Type k A B =
  is-coskeletal-function-type k (is-coskeletal-type-Coskeletal-Type B)

function-Coskeletal-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Coskeletal-Type l1 k)
  (B : Coskeletal-Type l2 k) → Coskeletal-Type (l1 ⊔ l2) k
pr1 (function-Coskeletal-Type k A B) = type-function-Coskeletal-Type k A B
pr2 (function-Coskeletal-Type k A B) =
  is-coskeletal-type-function-Coskeletal-Type k A B
```

### Products of coskeletal types are coskeletal

```agda
abstract
  is-coskeletal-product-Level :
    {l : Level} (k : 𝕋) {A B : UU l} →
    is-coskeletal k A → is-coskeletal k B → is-coskeletal k (A × B)
  is-coskeletal-product-Level k {A} {B} is-coskeletal-A is-coskeletal-B =
    is-coskeletal-equiv' k
      ( (b : bool) → rec-bool A B b)
      ( equiv-Π-bool-product (rec-bool A B))
      ( is-coskeletal-Π k
        ( ind-bool
          ( is-coskeletal k ∘ rec-bool A B)
          ( is-coskeletal-A)
          ( is-coskeletal-B)))

abstract
  is-coskeletal-product :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-coskeletal k A → is-coskeletal k B → is-coskeletal k (A × B)
  is-coskeletal-product {l1} {l2} k {A} {B} is-coskeletal-A is-coskeletal-B =
    is-coskeletal-equiv k (raise (l1 ⊔ l2) A × raise (l1 ⊔ l2) B)
      ( equiv-product (compute-raise (l1 ⊔ l2) A) (compute-raise (l1 ⊔ l2) B))
      ( is-coskeletal-product-Level k
        ( is-coskeletal-equiv' k A (compute-raise (l1 ⊔ l2) A) is-coskeletal-A)
        ( is-coskeletal-equiv' k B (compute-raise (l1 ⊔ l2) B) is-coskeletal-B))

product-Coskeletal-Type :
  {l1 l2 : Level} (k : 𝕋) →
  Coskeletal-Type l1 k → Coskeletal-Type l2 k → Coskeletal-Type (l1 ⊔ l2) k
pr1 (product-Coskeletal-Type k A B) =
  type-Coskeletal-Type A × type-Coskeletal-Type B
pr2 (product-Coskeletal-Type k A B) =
  is-coskeletal-product k
    ( is-coskeletal-type-Coskeletal-Type A)
    ( is-coskeletal-type-Coskeletal-Type B)

is-coskeletal-product' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-coskeletal (succ-𝕋 k) A) → (A → is-coskeletal (succ-𝕋 k) B) →
  is-coskeletal (succ-𝕋 k) (A × B)
is-coskeletal-product' k f g (a , b) (a' , b') =
  is-coskeletal-equiv k
    ( simplicial-hom-product (a , b) (a' , b'))
    ( compute-simplicial-hom-product)
    ( is-coskeletal-product k (f b a a') (g a b b'))

is-coskeletal-left-factor-product :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-coskeletal k (A × B) → B → is-coskeletal k A
is-coskeletal-left-factor-product neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-product A B H
is-coskeletal-left-factor-product (succ-𝕋 k) H b a a' =
  is-coskeletal-left-factor-product k {A = (a →₂ a')} {B = (b →₂ b)}
    ( is-coskeletal-equiv' k
      ( (a , b) →₂ (a' , b))
      ( compute-simplicial-hom-product)
      ( H (a , b) (a' , b)))
    ( id-simplicial-hom b)

is-coskeletal-right-factor-product :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-coskeletal k (A × B) → A → is-coskeletal k B
is-coskeletal-right-factor-product neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-product A B H
is-coskeletal-right-factor-product (succ-𝕋 k) {A} {B} H a b b' =
  is-coskeletal-right-factor-product k {A = (a →₂ a)} {B = (b →₂ b')}
    ( is-coskeletal-equiv' k
      ( (a , b) →₂ (a , b'))
      ( compute-simplicial-hom-product)
      ( H (a , b) (a , b')))
    ( id-simplicial-hom a)
```

### The type of equivalences between coskeletal types is coskeletal

```agda
-- module _
--   {l1 l2 : Level} {A : UU l1} {B : UU l2}
--   where

--   is-coskeletal-equiv-is-coskeletal :
--     (k : 𝕋) → is-coskeletal k A → is-coskeletal k B → is-coskeletal k (A ≃ B)
--   is-coskeletal-equiv-is-coskeletal k H K = {!   !}

-- type-equiv-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Coskeletal-Type l1 k) (B : Coskeletal-Type l2 k) →
--   UU (l1 ⊔ l2)
-- type-equiv-Coskeletal-Type A B =
--   type-Coskeletal-Type A ≃ type-Coskeletal-Type B

-- is-coskeletal-type-equiv-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Coskeletal-Type l1 k) (B : Coskeletal-Type l2 k) →
--   is-coskeletal k (type-equiv-Coskeletal-Type A B)
-- is-coskeletal-type-equiv-Coskeletal-Type A B =
--   is-coskeletal-equiv-is-coskeletal _
--     ( is-coskeletal-type-Coskeletal-Type A)
--     ( is-coskeletal-type-Coskeletal-Type B)

-- equiv-Coskeletal-Type :
--   {l1 l2 : Level} {k : 𝕋} (A : Coskeletal-Type l1 k) (B : Coskeletal-Type l2 k) →
--   Coskeletal-Type (l1 ⊔ l2) k
-- pr1 (equiv-Coskeletal-Type A B) = type-equiv-Coskeletal-Type A B
-- pr2 (equiv-Coskeletal-Type A B) = is-coskeletal-type-equiv-Coskeletal-Type A B
```
