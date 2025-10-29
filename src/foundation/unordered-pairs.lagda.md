# Unordered pairs of elements in a type

```agda
module foundation.unordered-pairs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.mere-equivalences
open import foundation.postcomposition-functions
open import foundation.propositional-truncations
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-function-types
open import foundation.universal-property-contractible-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.contractible-maps
open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.universal-property-standard-finite-types
```

</details>

## Idea

An unordered pair of elements in a type `A` consists of a 2-element type `X` and
a map `X → A`.

## Definition

### The definition of unordered pairs

```agda
unordered-pair : {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-pair A = Σ (2-Element-Type lzero) (λ X → type-2-Element-Type X → A)
```

### Immediate structure on the type of unordered pairs

```agda
module _
  {l : Level} {A : UU l} (p : unordered-pair A)
  where

  2-element-type-unordered-pair : 2-Element-Type lzero
  2-element-type-unordered-pair = pr1 p

  type-unordered-pair : UU lzero
  type-unordered-pair = type-2-Element-Type 2-element-type-unordered-pair

  has-two-elements-type-unordered-pair : has-two-elements type-unordered-pair
  has-two-elements-type-unordered-pair =
    has-two-elements-type-2-Element-Type 2-element-type-unordered-pair

  is-set-type-unordered-pair : is-set type-unordered-pair
  is-set-type-unordered-pair =
    is-set-mere-equiv' has-two-elements-type-unordered-pair (is-set-Fin 2)

  has-decidable-equality-type-unordered-pair :
    has-decidable-equality type-unordered-pair
  has-decidable-equality-type-unordered-pair =
    has-decidable-equality-mere-equiv'
      has-two-elements-type-unordered-pair
      ( has-decidable-equality-Fin 2)

  element-unordered-pair : type-unordered-pair → A
  element-unordered-pair = pr2 p

  other-element-unordered-pair : type-unordered-pair → A
  other-element-unordered-pair x =
    element-unordered-pair
      ( map-swap-2-Element-Type 2-element-type-unordered-pair x)
```

### The predicate of being in an unodered pair

```agda
is-in-unordered-pair-Prop :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) → Prop l
is-in-unordered-pair-Prop p a =
  exists-structure-Prop
    ( type-unordered-pair p)
    ( λ x → element-unordered-pair p x ＝ a)

is-in-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) → UU l
is-in-unordered-pair p a = type-Prop (is-in-unordered-pair-Prop p a)

is-prop-is-in-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) →
  is-prop (is-in-unordered-pair p a)
is-prop-is-in-unordered-pair p a =
  is-prop-type-Prop (is-in-unordered-pair-Prop p a)
```

### The condition of being a self-pairing

```agda
is-selfpairing-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) → UU l
is-selfpairing-unordered-pair p =
  (x y : type-unordered-pair p) →
  type-trunc-Prop (element-unordered-pair p x ＝ element-unordered-pair p y)
```

### Standard unordered pairs

Any two elements `x` and `y` in a type `A` define a standard unordered pair

```agda
module _
  {l1 : Level} {A : UU l1} (x y : A)
  where

  element-standard-unordered-pair : Fin 2 → A
  element-standard-unordered-pair =
    map-inv-ev-zero-one-Fin-2 (λ _ → A) (x , y)

  standard-unordered-pair : unordered-pair A
  pr1 standard-unordered-pair = Fin-Type-With-Cardinality-ℕ 2
  pr2 standard-unordered-pair = element-standard-unordered-pair

  other-element-standard-unordered-pair : Fin 2 → A
  other-element-standard-unordered-pair (inl (inr _)) = y
  other-element-standard-unordered-pair (inr _) = x

  compute-other-element-standard-unordered-pair :
    (u : Fin 2) →
    other-element-unordered-pair standard-unordered-pair u ＝
    other-element-standard-unordered-pair u
  compute-other-element-standard-unordered-pair (inl (inr x)) =
    ap element-standard-unordered-pair (compute-swap-Fin-2 (inl (inr x)))
  compute-other-element-standard-unordered-pair (inr x) =
    ap element-standard-unordered-pair (compute-swap-Fin-2 (inr x))
```

## Properties

### Extensionality of unordered pairs

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  Eq-unordered-pair : (p q : unordered-pair A) → UU l1
  Eq-unordered-pair p q =
    Σ ( type-unordered-pair p ≃ type-unordered-pair q)
      ( λ e →
        coherence-triangle-maps
          ( element-unordered-pair p)
          ( element-unordered-pair q)
          ( map-equiv e))

  refl-Eq-unordered-pair : (p : unordered-pair A) → Eq-unordered-pair p p
  pr1 (refl-Eq-unordered-pair (pair X p)) =
    id-equiv-Type-With-Cardinality-ℕ {k = 2} X
  pr2 (refl-Eq-unordered-pair (pair X p)) = refl-htpy

  Eq-eq-unordered-pair :
    (p q : unordered-pair A) → p ＝ q → Eq-unordered-pair p q
  Eq-eq-unordered-pair p .p refl = refl-Eq-unordered-pair p

  is-torsorial-Eq-unordered-pair :
    (p : unordered-pair A) →
    is-torsorial (Eq-unordered-pair p)
  is-torsorial-Eq-unordered-pair (pair X p) =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-Type-With-Cardinality-ℕ {k = 2} X)
      ( pair X (id-equiv-Type-With-Cardinality-ℕ {k = 2} X))
      ( is-torsorial-htpy p)

  is-equiv-Eq-eq-unordered-pair :
    (p q : unordered-pair A) → is-equiv (Eq-eq-unordered-pair p q)
  is-equiv-Eq-eq-unordered-pair p =
    fundamental-theorem-id
      ( is-torsorial-Eq-unordered-pair p)
      ( Eq-eq-unordered-pair p)

  extensionality-unordered-pair :
    (p q : unordered-pair A) → (p ＝ q) ≃ Eq-unordered-pair p q
  pr1 (extensionality-unordered-pair p q) = Eq-eq-unordered-pair p q
  pr2 (extensionality-unordered-pair p q) = is-equiv-Eq-eq-unordered-pair p q

  eq-Eq-unordered-pair' :
    (p q : unordered-pair A) → Eq-unordered-pair p q → p ＝ q
  eq-Eq-unordered-pair' p q =
    map-inv-is-equiv (is-equiv-Eq-eq-unordered-pair p q)

  eq-Eq-unordered-pair :
    (p q : unordered-pair A)
    (e : type-unordered-pair p ≃ type-unordered-pair q) →
    (element-unordered-pair p ~ (element-unordered-pair q ∘ map-equiv e)) →
    (p ＝ q)
  eq-Eq-unordered-pair p q e H = eq-Eq-unordered-pair' p q (pair e H)

  is-retraction-eq-Eq-unordered-pair :
    (p q : unordered-pair A) →
    (eq-Eq-unordered-pair' p q ∘ Eq-eq-unordered-pair p q) ~ id
  is-retraction-eq-Eq-unordered-pair p q =
    is-retraction-map-inv-is-equiv (is-equiv-Eq-eq-unordered-pair p q)

  is-section-eq-Eq-unordered-pair :
    (p q : unordered-pair A) →
    ( Eq-eq-unordered-pair p q ∘ eq-Eq-unordered-pair' p q) ~ id
  is-section-eq-Eq-unordered-pair p q =
    is-section-map-inv-is-equiv (is-equiv-Eq-eq-unordered-pair p q)

  eq-Eq-refl-unordered-pair :
    (p : unordered-pair A) → eq-Eq-unordered-pair p p id-equiv refl-htpy ＝ refl
  eq-Eq-refl-unordered-pair p = is-retraction-eq-Eq-unordered-pair p p refl
```

### Induction on equality of unordered pairs

```agda
module _
  {l1 l2 : Level} {A : UU l1} (p : unordered-pair A)
  (B : (q : unordered-pair A) → Eq-unordered-pair p q → UU l2)
  where

  ev-refl-Eq-unordered-pair :
    ((q : unordered-pair A) (e : Eq-unordered-pair p q) → B q e) →
    B p (refl-Eq-unordered-pair p)
  ev-refl-Eq-unordered-pair f = f p (refl-Eq-unordered-pair p)

  triangle-ev-refl-Eq-unordered-pair :
    coherence-triangle-maps
      ( ev-point (p , refl-Eq-unordered-pair p))
      ( ev-refl-Eq-unordered-pair)
      ( ev-pair)
  triangle-ev-refl-Eq-unordered-pair = refl-htpy

  abstract
    is-equiv-ev-refl-Eq-unordered-pair : is-equiv ev-refl-Eq-unordered-pair
    is-equiv-ev-refl-Eq-unordered-pair =
      is-equiv-right-map-triangle
        ( ev-point (p , refl-Eq-unordered-pair p))
        ( ev-refl-Eq-unordered-pair)
        ( ev-pair)
        ( triangle-ev-refl-Eq-unordered-pair)
        ( dependent-universal-property-contr-is-contr
          ( p , refl-Eq-unordered-pair p)
          ( is-torsorial-Eq-unordered-pair p)
          ( λ u → B (pr1 u) (pr2 u)))
        ( is-equiv-ev-pair)

  abstract
    is-contr-map-ev-refl-Eq-unordered-pair :
      is-contr-map ev-refl-Eq-unordered-pair
    is-contr-map-ev-refl-Eq-unordered-pair =
      is-contr-map-is-equiv is-equiv-ev-refl-Eq-unordered-pair

  abstract
    ind-Eq-unordered-pair :
      B p (refl-Eq-unordered-pair p) →
      ((q : unordered-pair A) (e : Eq-unordered-pair p q) → B q e)
    ind-Eq-unordered-pair u =
      pr1 (center (is-contr-map-ev-refl-Eq-unordered-pair u))

    compute-refl-ind-Eq-unordered-pair :
      (u : B p (refl-Eq-unordered-pair p)) →
      ind-Eq-unordered-pair u p (refl-Eq-unordered-pair p) ＝ u
    compute-refl-ind-Eq-unordered-pair u =
      pr2 (center (is-contr-map-ev-refl-Eq-unordered-pair u))
```

### Inverting extensional equality of unordered pairs

```agda
module _
  {l : Level} {A : UU l} (p q : unordered-pair A)
  where

  inv-Eq-unordered-pair :
    Eq-unordered-pair p q → Eq-unordered-pair q p
  pr1 (inv-Eq-unordered-pair (e , H)) = inv-equiv e
  pr2 (inv-Eq-unordered-pair (e , H)) =
    coherence-triangle-maps-inv-top
      ( element-unordered-pair p)
      ( element-unordered-pair q)
      ( e)
      ( H)
```

### Mere equality of unordered pairs

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  mere-Eq-unordered-pair-Prop : (p q : unordered-pair A) → Prop l1
  mere-Eq-unordered-pair-Prop p q = trunc-Prop (Eq-unordered-pair p q)

  mere-Eq-unordered-pair : (p q : unordered-pair A) → UU l1
  mere-Eq-unordered-pair p q = type-Prop (mere-Eq-unordered-pair-Prop p q)

  is-prop-mere-Eq-unordered-pair :
    (p q : unordered-pair A) → is-prop (mere-Eq-unordered-pair p q)
  is-prop-mere-Eq-unordered-pair p q =
    is-prop-type-Prop (mere-Eq-unordered-pair-Prop p q)

  refl-mere-Eq-unordered-pair :
    (p : unordered-pair A) → mere-Eq-unordered-pair p p
  refl-mere-Eq-unordered-pair p =
    unit-trunc-Prop (refl-Eq-unordered-pair p)
```

### A standard unordered pair `{x,y}` is equal to the standard unordered pair `{y,x}`

```agda
module _
  {l1 : Level} {A : UU l1} (x y : A)
  where

  swap-standard-unordered-pair :
    Eq-unordered-pair
      ( standard-unordered-pair x y)
      ( standard-unordered-pair y x)
  pr1 swap-standard-unordered-pair = equiv-succ-Fin 2
  pr2 swap-standard-unordered-pair (inl (inr _)) = refl
  pr2 swap-standard-unordered-pair (inr _) = refl

  is-commutative-standard-unordered-pair :
    standard-unordered-pair x y ＝ standard-unordered-pair y x
  is-commutative-standard-unordered-pair =
    eq-Eq-unordered-pair'
      ( standard-unordered-pair x y)
      ( standard-unordered-pair y x)
      ( swap-standard-unordered-pair)
```

### Dependent universal property of pointed unordered pairs

We will construct an equivalence

```text
  ((p : unordered-pair A) (i : type p) → B p i) ≃ ((x y : A) → B {x,y} 0)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (B : (p : unordered-pair A) → type-unordered-pair p → UU l2)
  where

  ev-pointed-unordered-pair :
    ((p : unordered-pair A) (i : type-unordered-pair p) → B p i) →
    ((x y : A) → B (standard-unordered-pair x y) (zero-Fin 1))
  ev-pointed-unordered-pair f x y =
    f (standard-unordered-pair x y) (zero-Fin 1)

  abstract
    dependent-universal-property-pointed-unordered-pairs :
      is-equiv ev-pointed-unordered-pair
    dependent-universal-property-pointed-unordered-pairs =
      is-equiv-comp
        ( λ f x y →
          f ( Fin-Type-With-Cardinality-ℕ 2)
            ( element-standard-unordered-pair x y)
            ( zero-Fin 1))
        ( ev-pair)
        ( is-equiv-ev-pair)
        ( is-equiv-comp
          ( λ f x y →
            f ( Fin-Type-With-Cardinality-ℕ 2)
              ( zero-Fin 1)
              ( element-standard-unordered-pair x y))
          ( map-Π (λ I → swap-Π))
          ( is-equiv-map-Π-is-fiberwise-equiv
            ( λ I → is-equiv-swap-Π))
          ( is-equiv-comp
            ( λ f x y → f (element-standard-unordered-pair x y))
            ( λ f → f (Fin-Type-With-Cardinality-ℕ 2) (zero-Fin 1))
            ( dependent-universal-property-identity-system-type-2-Element-Type
              ( Fin-Type-With-Cardinality-ℕ 2)
              ( zero-Fin 1)
              ( λ I i → (a : type-2-Element-Type I → A) → B (I , a) i))
            ( is-equiv-comp
              ( ev-pair)
              ( precomp-Π
                ( λ xy → element-standard-unordered-pair (pr1 xy) (pr2 xy))
                ( λ g →
                  B (Fin-Type-With-Cardinality-ℕ 2 , g) (zero-Fin 1)))
              ( is-equiv-precomp-Π-is-equiv
                ( is-equiv-map-inv-dependent-universal-proeprty-Fin-2
                  ( λ _ → A))
                ( λ g →
                  B (Fin-Type-With-Cardinality-ℕ 2 , g) (zero-Fin 1)))
              ( is-equiv-ev-pair))))

  equiv-dependent-universal-property-pointed-unordered-pairs :
    ((p : unordered-pair A) (i : type-unordered-pair p) → B p i) ≃
    ((x y : A) → B (standard-unordered-pair x y) (zero-Fin 1))
  pr1 equiv-dependent-universal-property-pointed-unordered-pairs =
    ev-pointed-unordered-pair
  pr2 equiv-dependent-universal-property-pointed-unordered-pairs =
    dependent-universal-property-pointed-unordered-pairs
```

### Functoriality of unordered pairs

```agda
map-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  unordered-pair A → unordered-pair B
pr1 (map-unordered-pair f p) = 2-element-type-unordered-pair p
pr2 (map-unordered-pair f p) = f ∘ element-unordered-pair p

preserves-comp-map-unordered-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-unordered-pair (g ∘ f) ~ (map-unordered-pair g ∘ map-unordered-pair f)
preserves-comp-map-unordered-pair g f p = refl

preserves-id-map-unordered-pair :
  {l1 : Level} {A : UU l1} →
  map-unordered-pair (id {A = A}) ~ id
preserves-id-map-unordered-pair = refl-htpy

htpy-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → (map-unordered-pair f ~ map-unordered-pair g)
htpy-unordered-pair {f = f} {g = g} H (pair X p) =
  eq-Eq-unordered-pair
    ( map-unordered-pair f (pair X p))
    ( map-unordered-pair g (pair X p))
    ( id-equiv)
    ( H ·r p)

preserves-refl-htpy-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  htpy-unordered-pair (refl-htpy {f = f}) ~ refl-htpy
preserves-refl-htpy-unordered-pair f p =
  is-retraction-eq-Eq-unordered-pair
    ( map-unordered-pair f p)
    ( map-unordered-pair f p)
    ( refl)

equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-pair A ≃ unordered-pair B)
equiv-unordered-pair e =
  equiv-tot (λ X → equiv-postcomp (type-Type-With-Cardinality-ℕ 2 X) e)

map-equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-pair A → unordered-pair B)
map-equiv-unordered-pair e = map-equiv (equiv-unordered-pair e)

is-equiv-map-equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-equiv (map-equiv-unordered-pair e)
is-equiv-map-equiv-unordered-pair e =
  is-equiv-map-equiv (equiv-unordered-pair e)

element-equiv-standard-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (x y : A) →
  ( map-equiv e ∘ element-standard-unordered-pair x y) ~
  ( element-standard-unordered-pair (map-equiv e x) (map-equiv e y))
element-equiv-standard-unordered-pair e x y (inl (inr _)) = refl
element-equiv-standard-unordered-pair e x y (inr _) = refl

equiv-standard-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (x y : A) →
  map-equiv-unordered-pair e (standard-unordered-pair x y) ＝
  standard-unordered-pair (map-equiv e x) (map-equiv e y)
equiv-standard-unordered-pair e x y =
  eq-Eq-unordered-pair
    ( map-equiv-unordered-pair e (standard-unordered-pair x y))
    ( standard-unordered-pair (map-equiv e x) (map-equiv e y))
    ( id-equiv)
    ( element-equiv-standard-unordered-pair e x y)

id-equiv-unordered-pair :
  {l : Level} {A : UU l} → map-equiv-unordered-pair (id-equiv {A = A}) ~ id
id-equiv-unordered-pair = refl-htpy

element-id-equiv-standard-unordered-pair :
  {l : Level} {A : UU l} (x y : A) →
  element-equiv-standard-unordered-pair (id-equiv {A = A}) x y ~ refl-htpy
element-id-equiv-standard-unordered-pair x y (inl (inr _)) = refl
element-id-equiv-standard-unordered-pair x y (inr _) = refl

id-equiv-standard-unordered-pair :
  {l : Level} {A : UU l} (x y : A) →
  equiv-standard-unordered-pair id-equiv x y ＝ refl
id-equiv-standard-unordered-pair x y =
  ( ap
    ( eq-Eq-unordered-pair
      ( standard-unordered-pair x y)
      ( standard-unordered-pair x y)
      ( id-equiv))
    ( eq-htpy (element-id-equiv-standard-unordered-pair x y))) ∙
  ( eq-Eq-refl-unordered-pair (standard-unordered-pair x y))

unordered-distinct-pair :
  {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-distinct-pair A =
  Σ (Type-With-Cardinality-ℕ lzero 2) (λ X → pr1 X ↪ A)
```

### Every unordered pair is merely equal to a standard unordered pair

```agda
abstract
  is-surjective-standard-unordered-pair :
    {l : Level} {A : UU l} (p : unordered-pair A) →
    type-trunc-Prop
      ( Σ A (λ x → Σ A (λ y → standard-unordered-pair x y ＝ p)))
  is-surjective-standard-unordered-pair (I , a) =
    map-trunc-Prop
      ( λ e →
        a (map-equiv e (zero-Fin 1)) ,
        a (map-equiv e (one-Fin 1)) ,
        eq-Eq-unordered-pair
          ( standard-unordered-pair _ _)
          ( I , a)
          ( e)
          ( λ where
            ( inl (inr _)) → refl
            ( inr _) → refl))
      ( has-two-elements-type-2-Element-Type I)
```

### For every unordered pair `p` and every element `i` in its underlying type, `p` is equal to a standard unordered pair

```agda
module _
  {l : Level} {A : UU l} (p : unordered-pair A) (i : type-unordered-pair p)
  where

  compute-standard-unordered-pair-element-unordered-pair :
    Eq-unordered-pair
      ( standard-unordered-pair
        ( element-unordered-pair p i)
        ( other-element-unordered-pair p i))
      ( p)
  pr1 compute-standard-unordered-pair-element-unordered-pair =
    equiv-point-2-Element-Type
      ( 2-element-type-unordered-pair p)
      ( i)
  pr2 compute-standard-unordered-pair-element-unordered-pair (inl (inr _)) =
    ap
      ( element-unordered-pair p)
      ( inv
        ( compute-map-equiv-point-2-Element-Type
          ( 2-element-type-unordered-pair p)
          ( i)))
  pr2 compute-standard-unordered-pair-element-unordered-pair (inr _) =
    ap
      ( element-unordered-pair p)
      ( inv
        ( compute-map-equiv-point-2-Element-Type'
          ( 2-element-type-unordered-pair p)
          ( i)))

  eq-compute-standard-unordered-pair-element-unordered-pair :
    standard-unordered-pair
      ( element-unordered-pair p i)
      ( other-element-unordered-pair p i) ＝ p
  eq-compute-standard-unordered-pair-element-unordered-pair =
    eq-Eq-unordered-pair'
      ( standard-unordered-pair
        ( element-unordered-pair p i)
        ( other-element-unordered-pair p i))
      ( p)
      ( compute-standard-unordered-pair-element-unordered-pair)
```
