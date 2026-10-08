# Double negation stable subtypes

```agda
module logic.double-negation-stable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.double-negation-stable-propositions
open import foundation.equality-dependent-function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.sets
open import foundation.structured-type-duality
open import foundation.subtypes
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import logic.double-negation-eliminating-maps
open import logic.double-negation-elimination
open import logic.double-negation-stable-embeddings
```

</details>

## Idea

A
{{#concept "double negation stable subtype" Disambiguation="of a type" Agda=is-double-negation-stable-subtype Agda=double-negation-stable-subtype}}
of a type consists of a family of
[double negation stable propositions](foundation.double-negation-stable-propositions.md)
over it.

## Definitions

### Double negation stable subtypes

```agda
is-double-negation-stable-subtype-Prop :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → Prop (l1 ⊔ l2)
is-double-negation-stable-subtype-Prop {A = A} P =
  Π-Prop A (λ a → is-double-negation-stable-Prop (P a))

is-double-negation-stable-subtype :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → UU (l1 ⊔ l2)
is-double-negation-stable-subtype P =
  type-Prop (is-double-negation-stable-subtype-Prop P)

is-prop-is-double-negation-stable-subtype :
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) →
  is-prop (is-double-negation-stable-subtype P)
is-prop-is-double-negation-stable-subtype P =
  is-prop-type-Prop (is-double-negation-stable-subtype-Prop P)

double-negation-stable-subtype :
  {l1 : Level} (l : Level) (X : UU l1) → UU (l1 ⊔ lsuc l)
double-negation-stable-subtype l X = X → Double-Negation-Stable-Prop l

make-double-negation-stable-subtype :
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) →
  is-double-negation-stable-subtype P →
  double-negation-stable-subtype l2 A
make-double-negation-stable-subtype P p x =
  ( is-in-subtype P x , is-prop-is-in-subtype P x , p x)
```

### The underlying subtype of a double negation stable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : double-negation-stable-subtype l2 A)
  where

  subtype-double-negation-stable-subtype : subtype l2 A
  subtype-double-negation-stable-subtype a =
    prop-Double-Negation-Stable-Prop (P a)

  is-double-negation-stable-double-negation-stable-subtype :
    is-double-negation-stable-subtype subtype-double-negation-stable-subtype
  is-double-negation-stable-double-negation-stable-subtype a =
    has-double-negation-elim-type-Double-Negation-Stable-Prop (P a)

  is-in-double-negation-stable-subtype : A → UU l2
  is-in-double-negation-stable-subtype =
    is-in-subtype subtype-double-negation-stable-subtype

  is-prop-is-in-double-negation-stable-subtype :
    (a : A) → is-prop (is-in-double-negation-stable-subtype a)
  is-prop-is-in-double-negation-stable-subtype =
    is-prop-is-in-subtype subtype-double-negation-stable-subtype
```

### The underlying type of a double negation stable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : double-negation-stable-subtype l2 A)
  where

  type-double-negation-stable-subtype : UU (l1 ⊔ l2)
  type-double-negation-stable-subtype =
    type-subtype (subtype-double-negation-stable-subtype P)

  inclusion-double-negation-stable-subtype :
    type-double-negation-stable-subtype → A
  inclusion-double-negation-stable-subtype =
    inclusion-subtype (subtype-double-negation-stable-subtype P)

  is-emb-inclusion-double-negation-stable-subtype :
    is-emb inclusion-double-negation-stable-subtype
  is-emb-inclusion-double-negation-stable-subtype =
    is-emb-inclusion-subtype (subtype-double-negation-stable-subtype P)

  is-double-negation-eliminating-map-inclusion-double-negation-stable-subtype :
    is-double-negation-eliminating-map inclusion-double-negation-stable-subtype
  is-double-negation-eliminating-map-inclusion-double-negation-stable-subtype
    x =
    has-double-negation-elim-equiv
      ( equiv-fiber-pr1 (type-Double-Negation-Stable-Prop ∘ P) x)
      ( has-double-negation-elim-type-Double-Negation-Stable-Prop (P x))

  is-injective-inclusion-double-negation-stable-subtype :
    is-injective inclusion-double-negation-stable-subtype
  is-injective-inclusion-double-negation-stable-subtype =
    is-injective-inclusion-subtype (subtype-double-negation-stable-subtype P)

  emb-double-negation-stable-subtype : type-double-negation-stable-subtype ↪ A
  emb-double-negation-stable-subtype =
    emb-subtype (subtype-double-negation-stable-subtype P)

  is-double-negation-stable-emb-inclusion-double-negation-stable-subtype :
    is-double-negation-stable-emb inclusion-double-negation-stable-subtype
  is-double-negation-stable-emb-inclusion-double-negation-stable-subtype =
    ( is-emb-inclusion-double-negation-stable-subtype ,
      is-double-negation-eliminating-map-inclusion-double-negation-stable-subtype)

  double-negation-stable-emb-double-negation-stable-subtype :
    type-double-negation-stable-subtype ↪¬¬ A
  double-negation-stable-emb-double-negation-stable-subtype =
    ( inclusion-double-negation-stable-subtype ,
      is-double-negation-stable-emb-inclusion-double-negation-stable-subtype)
```

### The double negation stable subtype associated to a double negation stable embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪¬¬ Y)
  where

  double-negation-stable-subtype-double-negation-stable-emb :
    double-negation-stable-subtype (l1 ⊔ l2) Y
  pr1 (double-negation-stable-subtype-double-negation-stable-emb y) =
    fiber (map-double-negation-stable-emb f) y
  pr2 (double-negation-stable-subtype-double-negation-stable-emb y) =
    is-double-negation-stable-prop-map-is-double-negation-stable-emb
      ( is-double-negation-stable-emb-map-double-negation-stable-emb f)
      ( y)

  compute-type-double-negation-stable-type-double-negation-stable-emb :
    type-double-negation-stable-subtype
      double-negation-stable-subtype-double-negation-stable-emb ≃
    X
  compute-type-double-negation-stable-type-double-negation-stable-emb =
    equiv-total-fiber (map-double-negation-stable-emb f)

  inv-compute-type-double-negation-stable-type-double-negation-stable-emb :
    X ≃
    type-double-negation-stable-subtype
      double-negation-stable-subtype-double-negation-stable-emb
  inv-compute-type-double-negation-stable-type-double-negation-stable-emb =
    inv-equiv-total-fiber (map-double-negation-stable-emb f)
```

## Examples

### The double negation stable subtypes of left and right elements in a coproduct type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-double-negation-stable-is-left :
    (x : A + B) → has-double-negation-elim (is-left x)
  is-double-negation-stable-is-left (inl x) = double-negation-elim-unit
  is-double-negation-stable-is-left (inr x) = double-negation-elim-empty

  is-left-Double-Negation-Stable-Prop :
    A + B → Double-Negation-Stable-Prop lzero
  pr1 (is-left-Double-Negation-Stable-Prop x) = is-left x
  pr1 (pr2 (is-left-Double-Negation-Stable-Prop x)) = is-prop-is-left x
  pr2 (pr2 (is-left-Double-Negation-Stable-Prop x)) =
    is-double-negation-stable-is-left x

  is-double-negation-stable-is-right :
    (x : A + B) → has-double-negation-elim (is-right x)
  is-double-negation-stable-is-right (inl x) = double-negation-elim-empty
  is-double-negation-stable-is-right (inr x) = double-negation-elim-unit

  is-right-Double-Negation-Stable-Prop :
    A + B → Double-Negation-Stable-Prop lzero
  pr1 (is-right-Double-Negation-Stable-Prop x) = is-right x
  pr1 (pr2 (is-right-Double-Negation-Stable-Prop x)) = is-prop-is-right x
  pr2 (pr2 (is-right-Double-Negation-Stable-Prop x)) =
    is-double-negation-stable-is-right x
```

## Properties

### A double negation stable subtype of a `k+1`-truncated type is `k+1`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (P : double-negation-stable-subtype l2 A)
  where

  abstract
    is-trunc-type-double-negation-stable-subtype :
      is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k)
      (type-double-negation-stable-subtype P)
    is-trunc-type-double-negation-stable-subtype =
      is-trunc-type-subtype k (subtype-double-negation-stable-subtype P)

module _
  {l1 l2 : Level} {A : UU l1} (P : double-negation-stable-subtype l2 A)
  where

  abstract
    is-prop-type-double-negation-stable-subtype :
      is-prop A → is-prop (type-double-negation-stable-subtype P)
    is-prop-type-double-negation-stable-subtype =
      is-prop-type-subtype (subtype-double-negation-stable-subtype P)

  abstract
    is-set-type-double-negation-stable-subtype :
      is-set A → is-set (type-double-negation-stable-subtype P)
    is-set-type-double-negation-stable-subtype =
      is-set-type-subtype (subtype-double-negation-stable-subtype P)

  abstract
    is-1-type-type-double-negation-stable-subtype :
      is-1-type A → is-1-type (type-double-negation-stable-subtype P)
    is-1-type-type-double-negation-stable-subtype =
      is-1-type-type-subtype (subtype-double-negation-stable-subtype P)

prop-double-negation-stable-subprop :
  {l1 l2 : Level} (A : Prop l1)
  (P : double-negation-stable-subtype l2 (type-Prop A)) →
  Prop (l1 ⊔ l2)
prop-double-negation-stable-subprop A P =
  prop-subprop A (subtype-double-negation-stable-subtype P)

set-double-negation-stable-subset :
  {l1 l2 : Level} (A : Set l1)
  (P : double-negation-stable-subtype l2 (type-Set A)) →
  Set (l1 ⊔ l2)
set-double-negation-stable-subset A P =
  set-subset A (subtype-double-negation-stable-subtype P)
```

### The type of double negation stable subtypes of a type is a set

```agda
is-set-double-negation-stable-subtype :
  {l1 l2 : Level} {X : UU l1} → is-set (double-negation-stable-subtype l2 X)
is-set-double-negation-stable-subtype =
  is-set-function-type is-set-Double-Negation-Stable-Prop
```

### Extensionality of the type of double negation stable subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : double-negation-stable-subtype l2 A)
  where

  has-same-elements-double-negation-stable-subtype :
    {l3 : Level} → double-negation-stable-subtype l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-double-negation-stable-subtype Q =
    has-same-elements-subtype
      ( subtype-double-negation-stable-subtype P)
      ( subtype-double-negation-stable-subtype Q)

  extensionality-double-negation-stable-subtype :
    (Q : double-negation-stable-subtype l2 A) →
    (P ＝ Q) ≃ has-same-elements-double-negation-stable-subtype Q
  extensionality-double-negation-stable-subtype =
    extensionality-Π P
      ( λ x Q →
        ( type-Double-Negation-Stable-Prop (P x)) ↔
        ( type-Double-Negation-Stable-Prop Q))
      ( λ x Q → extensionality-Double-Negation-Stable-Prop (P x) Q)

  has-same-elements-eq-double-negation-stable-subtype :
    (Q : double-negation-stable-subtype l2 A) →
    (P ＝ Q) → has-same-elements-double-negation-stable-subtype Q
  has-same-elements-eq-double-negation-stable-subtype Q =
    map-equiv (extensionality-double-negation-stable-subtype Q)

  eq-has-same-elements-double-negation-stable-subtype :
    (Q : double-negation-stable-subtype l2 A) →
    has-same-elements-double-negation-stable-subtype Q → P ＝ Q
  eq-has-same-elements-double-negation-stable-subtype Q =
    map-inv-equiv (extensionality-double-negation-stable-subtype Q)

  refl-extensionality-double-negation-stable-subtype :
    map-equiv (extensionality-double-negation-stable-subtype P) refl ＝
    (λ x → id , id)
  refl-extensionality-double-negation-stable-subtype = refl
```

### The type of double negation stable subtypes of `A` is equivalent to the type of all double negation stable embeddings into a type `A`

```agda
equiv-Fiber-Double-Negation-Stable-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Σ (UU (l1 ⊔ l)) (λ X → X ↪¬¬ A) ≃ (double-negation-stable-subtype (l1 ⊔ l) A)
equiv-Fiber-Double-Negation-Stable-Prop l A =
  ( equiv-Fiber-structure l is-double-negation-stable-prop A) ∘e
  ( equiv-tot
    ( λ X →
      equiv-tot
        ( λ f →
          ( inv-distributive-Π-Σ) ∘e
          ( equiv-product-left (equiv-is-prop-map-is-emb f)))))
```
