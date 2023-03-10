# Unordered pairs of elements in a type

```agda
module foundation.unordered-pairs where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

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
  ∃-Prop (type-unordered-pair p) (λ x → element-unordered-pair p x ＝ a)

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
  {l1 : Level} {A : UU l1}
  where

  element-standard-unordered-pair : (x y : A) → Fin 2 → A
  element-standard-unordered-pair x y (inl (inr star)) = x
  element-standard-unordered-pair x y (inr star) = y

  standard-unordered-pair : A → A → unordered-pair A
  pr1 (standard-unordered-pair x y) = Fin-UU-Fin' 2
  pr2 (standard-unordered-pair x y) = element-standard-unordered-pair x y
```

## Properties

### Equality of unordered pairs

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  Eq-unordered-pair : (p q : unordered-pair A) → UU l1
  Eq-unordered-pair p q =
    Σ ( type-unordered-pair p ≃ type-unordered-pair q)
      ( λ e → (element-unordered-pair p) ~ (element-unordered-pair q ∘ map-equiv e))

  refl-Eq-unordered-pair : (p : unordered-pair A) → Eq-unordered-pair p p
  pr1 (refl-Eq-unordered-pair (pair X p)) = id-equiv-UU-Fin {k = 2} X
  pr2 (refl-Eq-unordered-pair (pair X p)) = refl-htpy

  Eq-eq-unordered-pair :
    (p q : unordered-pair A) → p ＝ q → Eq-unordered-pair p q
  Eq-eq-unordered-pair p .p refl = refl-Eq-unordered-pair p

  is-contr-total-Eq-unordered-pair :
    (p : unordered-pair A) →
    is-contr (Σ (unordered-pair A) (Eq-unordered-pair p))
  is-contr-total-Eq-unordered-pair (pair X p) =
    is-contr-total-Eq-structure
      ( λ Y q e → p ~ (q ∘ map-equiv e))
      ( is-contr-total-equiv-UU-Fin {k = 2} X)
      ( pair X (id-equiv-UU-Fin {k = 2} X))
      ( is-contr-total-htpy p)

  is-equiv-Eq-eq-unordered-pair :
    (p q : unordered-pair A) → is-equiv (Eq-eq-unordered-pair p q)
  is-equiv-Eq-eq-unordered-pair p =
    fundamental-theorem-id
      ( is-contr-total-Eq-unordered-pair p)
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
    (p q : unordered-pair A) (e : type-unordered-pair p ≃ type-unordered-pair q) →
    (element-unordered-pair p ~ (element-unordered-pair q ∘ map-equiv e)) → (p ＝ q)
  eq-Eq-unordered-pair p q e H = eq-Eq-unordered-pair' p q (pair e H)

  isretr-eq-Eq-unordered-pair :
    (p q : unordered-pair A) →
    (eq-Eq-unordered-pair' p q ∘ Eq-eq-unordered-pair p q) ~ id
  isretr-eq-Eq-unordered-pair p q =
    isretr-map-inv-is-equiv (is-equiv-Eq-eq-unordered-pair p q)

  issec-eq-Eq-unordered-pair :
    (p q : unordered-pair A) →
    ( Eq-eq-unordered-pair p q ∘ eq-Eq-unordered-pair' p q) ~ id
  issec-eq-Eq-unordered-pair p q =
    issec-map-inv-is-equiv (is-equiv-Eq-eq-unordered-pair p q)

  eq-Eq-refl-unordered-pair :
    (p : unordered-pair A) → eq-Eq-unordered-pair p p id-equiv refl-htpy ＝ refl
  eq-Eq-refl-unordered-pair p = isretr-eq-Eq-unordered-pair p p refl
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

### A standard unordered pair `{x,y}` is equal to the standard unordered pair `{y,x}`.

```agda
is-commutative-standard-unordered-pair :
  {l : Level} {A : UU l} (x y : A) →
  standard-unordered-pair x y ＝ standard-unordered-pair y x
is-commutative-standard-unordered-pair x y =
  eq-Eq-unordered-pair
    ( standard-unordered-pair x y)
    ( standard-unordered-pair y x)
    ( equiv-succ-Fin 2)
    ( λ { (inl (inr star)) → refl ; (inr star) → refl})
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
  isretr-eq-Eq-unordered-pair
    ( map-unordered-pair f p)
    ( map-unordered-pair f p)
    ( refl)

equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-pair A ≃ unordered-pair B)
equiv-unordered-pair e = equiv-tot (λ X → equiv-postcomp (type-UU-Fin 2 X) e)

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
element-equiv-standard-unordered-pair e x y (inl (inr star)) = refl
element-equiv-standard-unordered-pair e x y (inr star) = refl

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
element-id-equiv-standard-unordered-pair x y (inl (inr star)) = refl
element-id-equiv-standard-unordered-pair x y (inr star) = refl

id-equiv-standard-unordered-pair :
  {l : Level} {A : UU l} (x y : A) → equiv-standard-unordered-pair id-equiv x y ＝ refl
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
unordered-distinct-pair A = Σ (UU-Fin lzero 2) (λ X → pr1 X ↪ A)
```
