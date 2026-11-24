# Subtypes

```agda
module foundation-core.subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A **subtype** of a type `A` is a family of
[propositions](foundation-core.propositions.md) over `A`. The underlying type of
a subtype `P` of `A` is the [total space](foundation.dependent-pair-types.md)
`Σ A B`.

## Definitions

### Subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-subtype : UU (l1 ⊔ l2)
  is-subtype = (x : A) → is-prop (B x)

  is-property : UU (l1 ⊔ l2)
  is-property = is-subtype

subtype : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
subtype l A = A → Prop l

module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  is-in-subtype : A → UU l2
  is-in-subtype x = type-Prop (P x)

  is-prop-is-in-subtype : (x : A) → is-prop (is-in-subtype x)
  is-prop-is-in-subtype x = is-prop-type-Prop (P x)

  type-subtype : UU (l1 ⊔ l2)
  type-subtype = Σ A is-in-subtype

  inclusion-subtype : type-subtype → A
  inclusion-subtype = pr1

  ap-inclusion-subtype :
    (x y : type-subtype) →
    x ＝ y → (inclusion-subtype x ＝ inclusion-subtype y)
  ap-inclusion-subtype x y p = ap inclusion-subtype p

  is-in-subtype-inclusion-subtype :
    (x : type-subtype) → is-in-subtype (inclusion-subtype x)
  is-in-subtype-inclusion-subtype = pr2

  eq-is-in-subtype :
    {x : A} {p q : is-in-subtype x} → p ＝ q
  eq-is-in-subtype {x} = eq-is-prop (is-prop-is-in-subtype x)

  is-closed-under-eq-subtype :
    {x y : A} → is-in-subtype x → (x ＝ y) → is-in-subtype y
  is-closed-under-eq-subtype p refl = p

  is-closed-under-eq-subtype' :
    {x y : A} → is-in-subtype y → (x ＝ y) → is-in-subtype x
  is-closed-under-eq-subtype' p refl = p
```

### The containment relation on subtypes

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  leq-prop-subtype :
    {l2 l3 : Level} → subtype l2 A → subtype l3 A → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-subtype P Q =
    Π-Prop A (λ x → hom-Prop (P x) (Q x))

  infix 5 _⊆_
  _⊆_ :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → UU (l1 ⊔ l2 ⊔ l3)
  P ⊆ Q = type-Prop (leq-prop-subtype P Q)

  is-prop-leq-subtype :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → is-prop (P ⊆ Q)
  is-prop-leq-subtype P Q =
    is-prop-type-Prop (leq-prop-subtype P Q)

  inclusion-leq-subtype :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → P ⊆ Q →
    type-subtype P → type-subtype Q
  inclusion-leq-subtype P Q P⊆Q (x , x∈P) = (x , P⊆Q x x∈P)
```

## Properties

### The containment relation on subtypes is a preordering

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  refl-leq-subtype : {l2 : Level} (P : subtype l2 A) → P ⊆ P
  refl-leq-subtype P x = id

  transitive-leq-subtype :
    {l2 l3 l4 : Level}
    (P : subtype l2 A) (Q : subtype l3 A) (R : subtype l4 A) →
    Q ⊆ R → P ⊆ Q → P ⊆ R
  transitive-leq-subtype P Q R H K x = H x ∘ K x
```

### Equality in subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  Eq-type-subtype : (x y : type-subtype P) → UU l1
  Eq-type-subtype x y = (pr1 x ＝ pr1 y)

  extensionality-type-subtype' :
    (a b : type-subtype P) → (a ＝ b) ≃ (pr1 a ＝ pr1 b)
  extensionality-type-subtype' (a , p) =
    extensionality-type-subtype P p refl (λ x → id-equiv)

  eq-type-subtype :
    {a b : type-subtype P} → (pr1 a ＝ pr1 b) → a ＝ b
  eq-type-subtype {a} {b} = map-inv-equiv (extensionality-type-subtype' a b)
```

### If `B` is a subtype of `A`, then the projection map `Σ A B → A` is a propositional map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : subtype l2 A)
  where

  abstract
    is-prop-map-inclusion-subtype : is-prop-map (inclusion-subtype B)
    is-prop-map-inclusion-subtype =
      ( λ x →
        is-prop-equiv
          ( equiv-fiber-pr1 (is-in-subtype B) x)
          ( is-prop-is-in-subtype B x))

  prop-map-subtype : prop-map (type-subtype B) A
  pr1 prop-map-subtype = inclusion-subtype B
  pr2 prop-map-subtype = is-prop-map-inclusion-subtype
```

### If `B` is a subtype of `A`, then the projection map `Σ A B → A` is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : subtype l2 A)
  where

  abstract
    is-emb-inclusion-subtype : is-emb (inclusion-subtype B)
    is-emb-inclusion-subtype =
      is-emb-is-prop-map
        ( is-prop-map-inclusion-subtype B)

  emb-subtype : type-subtype B ↪ A
  pr1 emb-subtype = inclusion-subtype B
  pr2 emb-subtype = is-emb-inclusion-subtype

  injection-subtype : injection (type-subtype B) A
  injection-subtype = injection-emb emb-subtype

  equiv-ap-inclusion-subtype :
    {s t : type-subtype B} →
    (s ＝ t) ≃ (inclusion-subtype B s ＝ inclusion-subtype B t)
  pr1 (equiv-ap-inclusion-subtype {s} {t}) = ap-inclusion-subtype B s t
  pr2 (equiv-ap-inclusion-subtype {s} {t}) = is-emb-inclusion-subtype s t
```

### Restriction of a `k`-truncated map to a `k`-truncated map into a subtype

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} (B : subtype l2 A) {X : UU l3}
  where

  abstract
    is-trunc-map-into-subtype :
      {f : X → A} → is-trunc-map k f →
      (p : (x : X) → is-in-subtype B (f x)) →
      is-trunc-map k {B = type-subtype B} (λ x → (f x , p x))
    is-trunc-map-into-subtype H p (a , b) =
      is-trunc-equiv k _
        ( equiv-tot (λ x → extensionality-type-subtype' B _ _))
        ( H a)

  trunc-map-into-subtype :
    (f : trunc-map k X A) → ((x : X) → is-in-subtype B (map-trunc-map f x)) →
    trunc-map k X (type-subtype B)
  pr1 (trunc-map-into-subtype f p) x = (map-trunc-map f x , p x)
  pr2 (trunc-map-into-subtype f p) =
    is-trunc-map-into-subtype
      ( is-trunc-map-map-trunc-map f)
      ( p)
```

### Restriction of an embedding to an embedding into a subtype

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : subtype l2 A) {X : UU l3} (f : X ↪ A)
  (p : (x : X) → is-in-subtype B (map-emb f x))
  where

  map-emb-into-subtype : X → type-subtype B
  pr1 (map-emb-into-subtype x) = map-emb f x
  pr2 (map-emb-into-subtype x) = p x

  abstract
    is-emb-map-emb-into-subtype : is-emb map-emb-into-subtype
    is-emb-map-emb-into-subtype =
      is-emb-is-prop-map
        ( is-trunc-map-into-subtype
          ( neg-one-𝕋)
          ( B)
          ( is-prop-map-is-emb (is-emb-map-emb f))
          ( p))

  emb-into-subtype : X ↪ type-subtype B
  pr1 emb-into-subtype = map-emb-into-subtype
  pr2 emb-into-subtype = is-emb-map-emb-into-subtype
```

### If the projection map of a type family is an embedding, then the type family is a subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-subtype-is-emb-pr1 : is-emb (pr1 {B = B}) → is-subtype B
    is-subtype-is-emb-pr1 H x =
      is-prop-equiv' (equiv-fiber-pr1 B x) (is-prop-map-is-emb H x)
```

### A subtype of a `k+1`-truncated type is `k+1`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (P : subtype l2 A)
  where

  abstract
    is-trunc-type-subtype :
      is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (type-subtype P)
    is-trunc-type-subtype =
      is-trunc-is-emb k
        ( inclusion-subtype P)
        ( is-emb-inclusion-subtype P)

module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  abstract
    is-prop-type-subtype : is-prop A → is-prop (type-subtype P)
    is-prop-type-subtype = is-trunc-type-subtype neg-two-𝕋 P

  abstract
    is-set-type-subtype : is-set A → is-set (type-subtype P)
    is-set-type-subtype = is-trunc-type-subtype neg-one-𝕋 P

prop-subprop :
  {l1 l2 : Level} (A : Prop l1) (P : subtype l2 (type-Prop A)) → Prop (l1 ⊔ l2)
pr1 (prop-subprop A P) = type-subtype P
pr2 (prop-subprop A P) = is-prop-type-subtype P (is-prop-type-Prop A)

set-subset :
  {l1 l2 : Level} (A : Set l1) (P : subtype l2 (type-Set A)) → Set (l1 ⊔ l2)
pr1 (set-subset A P) = type-subtype P
pr2 (set-subset A P) = is-set-type-subtype P (is-set-type-Set A)
```

### Logically equivalent subtypes induce equivalences on the underlying type of a subtype

```agda
equiv-type-subtype :
  { l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2} {Q : A → UU l3} →
  ( is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q) →
  ( f : (x : A) → P x → Q x) →
  ( g : (x : A) → Q x → P x) →
  ( Σ A P) ≃ (Σ A Q)
pr1 (equiv-type-subtype is-subtype-P is-subtype-Q f g) = tot f
pr2 (equiv-type-subtype is-subtype-P is-subtype-Q f g) =
  is-equiv-tot-is-fiberwise-equiv
    ( λ x →
      is-equiv-has-converse-is-prop
        ( is-subtype-P x)
        ( is-subtype-Q x)
        ( g x))
```

### Equivalences of subtypes

```agda
equiv-subtype-equiv :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (e : A ≃ B)
  (C : A → Prop l3) (D : B → Prop l4) →
  ((x : A) → type-Prop (C x) ↔ type-Prop (D (map-equiv e x))) →
  type-subtype C ≃ type-subtype D
equiv-subtype-equiv e C D H =
  equiv-Σ (type-Prop ∘ D) e (λ x → equiv-iff' (C x) (D (map-equiv e x)) (H x))
```

```agda
abstract
  is-equiv-subtype-is-equiv :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv {Q = Q} is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q is-equiv-f
      ( λ x →
        is-equiv-has-converse-is-prop
          ( is-subtype-P x)
          ( is-subtype-Q (f x))
          ( h x))

abstract
  is-equiv-subtype-is-equiv' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    (is-equiv-f : is-equiv f) →
    ((y : B) → Q y → P (map-inv-is-equiv is-equiv-f y)) →
    is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv' {P = P} {Q}
    is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q is-equiv-f
      ( λ x →
        is-equiv-has-converse-is-prop
          ( is-subtype-P x)
          ( is-subtype-Q (f x))
          ( (tr P (is-retraction-map-inv-is-equiv is-equiv-f x)) ∘ (h (f x))))
```
