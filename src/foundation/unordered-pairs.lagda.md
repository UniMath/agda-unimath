# Unordered pairs of elements in a type

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.unordered-pairs where

open import foundation.contractible-types using (is-contr)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-equality using (has-decidable-equality)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (_↪_)
open import foundation.equivalences using
  ( map-equiv; is-equiv; _≃_; map-inv-is-equiv; isretr-map-inv-is-equiv;
    id-equiv; is-equiv-map-equiv)
open import foundation.existential-quantification using (∃)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-function-types using (equiv-postcomp)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using
  ( _~_; refl-htpy; is-contr-total-htpy; _·r_)
open import foundation.identity-types using (Id; refl)
open import foundation.mere-equivalences using
  ( mere-equiv; is-set-mere-equiv'; has-decidable-equality-mere-equiv')
open import foundation.propositional-truncations using
  ( type-trunc-Prop; trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.sets using (is-set)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; lzero; lsuc; _⊔_)

open import univalent-combinatorics.2-element-types using
  ( 2-Element-Type; type-2-Element-Type; map-swap-2-Element-Type;
    has-two-elements; has-two-elements-type-2-Element-Type)
open import univalent-combinatorics.equality-standard-finite-types using
  ( is-set-Fin; has-decidable-equality-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin; Fin-UU-Fin; equiv-UU-Fin; id-equiv-UU-Fin;
    is-contr-total-equiv-UU-Fin; type-UU-Fin)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; equiv-succ-Fin)
```

## Idea

An unordered pair of elements in a type `A` consists of a 2-element type `X` and a map `X → A`.

## Definition

### The definition of unordered pairs

```
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
      has-decidable-equality-Fin

  element-unordered-pair : type-unordered-pair → A
  element-unordered-pair = pr2 p

  other-element-unordered-pair : type-unordered-pair → A
  other-element-unordered-pair x =
    element-unordered-pair
      ( map-swap-2-Element-Type 2-element-type-unordered-pair x)
```

### The predicate of being in an unodered pair

```agda
is-in-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) → UU l
is-in-unordered-pair p a = ∃ (type-unordered-pair p) (λ x → Id (element-unordered-pair p x) a)
```

### The condition of being a self-pairing

```agda
is-selfpairing-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) → UU l
is-selfpairing-unordered-pair p =
  (x y : type-unordered-pair p) →
  type-trunc-Prop (Id (element-unordered-pair p x) (element-unordered-pair p y))
```

### Standard unordered pairs

Any two elements `x` and `y` in a type `A` define a standard unordered pair

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  standard-unordered-pair : A → A → unordered-pair A
  pr1 (standard-unordered-pair x y) = Fin-UU-Fin 2
  pr2 (standard-unordered-pair x y) (inl (inr star)) = x
  pr2 (standard-unordered-pair x y) (inr star) = y
```

## Properties

### Equality of unordered pairs

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  Eq-unordered-pair : (p q : unordered-pair A) → UU l1
  Eq-unordered-pair (pair X p) (pair Y q) =
    Σ (equiv-UU-Fin X Y) (λ e → p ~ (q ∘ map-equiv e))

  refl-Eq-unordered-pair : (p : unordered-pair A) → Eq-unordered-pair p p
  pr1 (refl-Eq-unordered-pair (pair X p)) = id-equiv-UU-Fin X
  pr2 (refl-Eq-unordered-pair (pair X p)) = refl-htpy

  Eq-eq-unordered-pair :
    (p q : unordered-pair A) → Id p q → Eq-unordered-pair p q
  Eq-eq-unordered-pair p .p refl = refl-Eq-unordered-pair p

  is-contr-total-Eq-unordered-pair :
    (p : unordered-pair A) →
    is-contr (Σ (unordered-pair A) (Eq-unordered-pair p))
  is-contr-total-Eq-unordered-pair (pair X p) =
    is-contr-total-Eq-structure
      ( λ Y q e → p ~ (q ∘ map-equiv e))
      ( is-contr-total-equiv-UU-Fin X)
      ( pair X (id-equiv-UU-Fin X))
      ( is-contr-total-htpy p)

  is-equiv-Eq-eq-unordered-pair :
    (p q : unordered-pair A) → is-equiv (Eq-eq-unordered-pair p q)
  is-equiv-Eq-eq-unordered-pair p =
    fundamental-theorem-id p
      ( refl-Eq-unordered-pair p)
      ( is-contr-total-Eq-unordered-pair p)
      ( Eq-eq-unordered-pair p)

  extensionality-unordered-pair :
    (p q : unordered-pair A) → Id p q ≃ Eq-unordered-pair p q
  pr1 (extensionality-unordered-pair p q) = Eq-eq-unordered-pair p q
  pr2 (extensionality-unordered-pair p q) = is-equiv-Eq-eq-unordered-pair p q

  eq-Eq-unordered-pair :
    (p q : unordered-pair A) → Eq-unordered-pair p q → Id p q
  eq-Eq-unordered-pair p q =
    map-inv-is-equiv (is-equiv-Eq-eq-unordered-pair p q)

  isretr-eq-Eq-unordered-pair :
    (p q : unordered-pair A) →
    (eq-Eq-unordered-pair p q ∘ Eq-eq-unordered-pair p q) ~ id
  isretr-eq-Eq-unordered-pair p q =
    isretr-map-inv-is-equiv (is-equiv-Eq-eq-unordered-pair p q)
```

### Mere equality of unordered pairs

```agda
module _
  {l1 : Level} {A : UU l1}
  where
  
  mere-Eq-unordered-pair-Prop : (p q : unordered-pair A) → UU-Prop l1
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

### A standard unordered pair `{x,y}` is equal to the standard unordered pair `{y,x}`.

```agda
is-commutative-standard-unordered-pair :
  {l : Level} {A : UU l} (x y : A) →
  Id (standard-unordered-pair x y) (standard-unordered-pair y x)
is-commutative-standard-unordered-pair x y =
  eq-Eq-unordered-pair
    ( standard-unordered-pair x y)
    ( standard-unordered-pair y x)
    ( pair equiv-succ-Fin (λ { (inl (inr star)) → refl ; (inr star) → refl}))
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
    ( pair id-equiv (H ·r p))

preserves-refl-htpy-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  htpy-unordered-pair (refl-htpy {f = f}) ~ refl-htpy
preserves-refl-htpy-unordered-pair f p =
  isretr-eq-Eq-unordered-pair
    ( map-unordered-pair f p)
    ( map-unordered-pair f p)
    ( refl)

equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-pair A ≃ unordered-pair B)
equiv-unordered-pair e = equiv-tot (λ X → equiv-postcomp (type-UU-Fin X) e)

map-equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-pair A → unordered-pair B)
map-equiv-unordered-pair e = map-equiv (equiv-unordered-pair e)

is-equiv-map-equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-equiv (map-equiv-unordered-pair e)
is-equiv-map-equiv-unordered-pair e =
  is-equiv-map-equiv (equiv-unordered-pair e)

unordered-distinct-pair :
  {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-distinct-pair A = Σ (UU-Fin 2) (λ X → pr1 X ↪ A)
```
