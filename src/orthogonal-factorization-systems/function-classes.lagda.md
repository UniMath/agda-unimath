# Function classes

```agda
module orthogonal-factorization-systems.function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-induction
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.pullback-squares
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

A **function class** is a [subtype](foundation.subtypes.md) of the type of all
functions in a given universe.

## Definitions

```agda
function-class : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
function-class l1 l2 l3 = {A : UU l1} {B : UU l2} → subtype l3 (A → B)

module _
  {l1 l2 l3 : Level} (P : function-class l1 l2 l3)
  where

  is-in-function-class : {A : UU l1} {B : UU l2} → (A → B) → UU l3
  is-in-function-class = is-in-subtype P

  is-prop-is-in-function-class :
    {A : UU l1} {B : UU l2} → (f : A → B) → is-prop (is-in-function-class f)
  is-prop-is-in-function-class = is-prop-is-in-subtype P

  type-function-class : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2 ⊔ l3)
  type-function-class A B = type-subtype (P {A} {B})

  inclusion-function-class :
    {A : UU l1} {B : UU l2} → type-function-class A B → A → B
  inclusion-function-class = inclusion-subtype P

  is-emb-inclusion-function-class :
    {A : UU l1} {B : UU l2} → is-emb (inclusion-function-class {A} {B})
  is-emb-inclusion-function-class = is-emb-inclusion-subtype P

  emb-function-class :
    {A : UU l1} {B : UU l2} → type-function-class A B ↪ (A → B)
  emb-function-class = emb-subtype P
```

### Function classes containing the identities

```agda
has-identity-maps-function-class :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
has-identity-maps-function-class {l1} {l2} P =
  (A : UU l1) → is-in-function-class P (id {A = A})

has-identity-maps-function-class-Prop :
  {l1 l2 : Level} → function-class l1 l1 l2 → Prop (lsuc l1 ⊔ l2)
has-identity-maps-function-class-Prop {l1} P =
  Π-Prop (UU l1) λ A → P (id {A = A})

is-prop-has-identity-maps-function-class :
  {l1 l2 : Level} (P : function-class l1 l1 l2) →
  is-prop (has-identity-maps-function-class P)
is-prop-has-identity-maps-function-class =
  is-prop-type-Prop ∘ has-identity-maps-function-class-Prop
```

### Function classes containing the equivalences

```agda
has-equivalences-function-class :
  {l1 l2 l3 : Level} → function-class l1 l2 l3 → UU (lsuc l1 ⊔ lsuc l2 ⊔ l3)
has-equivalences-function-class {l1} {l2} P =
  (A : UU l1) (B : UU l2) (f : A → B) → is-equiv f → is-in-function-class P f

has-equivalences-function-class-Prop :
  {l1 l2 l3 : Level} → function-class l1 l2 l3 → Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3)
has-equivalences-function-class-Prop {l1} {l2} {l3} P =
  Π-Prop (UU l1) λ A → Π-Prop (UU l2) λ B → Π-Prop (A → B)
    ( λ f → function-Prop (is-equiv f) (P f))

is-prop-has-equivalences-function-class :
  {l1 l2 l3 : Level} (P : function-class l1 l2 l3) →
  is-prop (has-equivalences-function-class P)
is-prop-has-equivalences-function-class =
  is-prop-type-Prop ∘ has-equivalences-function-class-Prop
```

### Composition closed function classes

We say a function class is **composition closed** if it is closed under taking
composites.

```agda
is-closed-under-composition-function-class :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
is-closed-under-composition-function-class {l1} {l2} P =
  (A B C : UU l1) (f : A → B) (g : B → C) →
  is-in-function-class P f → is-in-function-class P g →
  is-in-function-class P (g ∘ f)

composition-closed-function-class :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
composition-closed-function-class l1 l2 =
  Σ (function-class l1 l1 l2) (is-closed-under-composition-function-class)

is-prop-is-closed-under-composition-function-class :
  {l1 l2 : Level} (P : function-class l1 l1 l2) →
  is-prop (is-closed-under-composition-function-class P)
is-prop-is-closed-under-composition-function-class P =
  is-prop-iterated-Π 7
    ( λ A B C f g _ _ → is-prop-is-in-function-class P (g ∘ f))

is-closed-under-composition-function-class-Prop :
  {l1 l2 : Level} → function-class l1 l1 l2 → Prop (lsuc l1 ⊔ l2)
pr1 (is-closed-under-composition-function-class-Prop P) =
  is-closed-under-composition-function-class P
pr2 (is-closed-under-composition-function-class-Prop P) =
  is-prop-is-closed-under-composition-function-class P
```

## Pullback-stable function classes

A function class is said to be **pullback-stable** if given a function in it,
then its pullback along any map is also in the function class.

```agda
is-pullback-stable-function-class :
  {l1 l2 l3 : Level} (l : Level) → function-class l1 l2 l3 →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l)
is-pullback-stable-function-class {l1} {l2} l P =
  (A : UU l1) (B C : UU l2) (f : A → C) (g : B → C)
  (p : Σ (UU l1) (pullback-cone l f g)) →
  is-in-function-class P f →
  is-in-function-class P (horizontal-map-pullback-cone f g (pr2 p))

pullback-stable-function-class :
  (l1 l2 l3 l4 : Level) → UU (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4))
pullback-stable-function-class l1 l2 l3 l4 =
  Σ (function-class l1 l2 l3) (is-pullback-stable-function-class l4)

is-prop-is-pullback-stable-function-class :
  {l1 l2 l3 : Level} (l : Level) (P : function-class l1 l2 l3) →
  is-prop (is-pullback-stable-function-class l P)
is-prop-is-pullback-stable-function-class l P =
  is-prop-iterated-Π 7
    ( λ A B C f g p _ →
      is-prop-is-in-function-class P (horizontal-map-pullback-cone f g (pr2 p)))

is-pullback-stable-function-class-Prop :
  {l1 l2 l3 : Level} (l : Level) (P : function-class l1 l2 l3) →
  Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l)
pr1 (is-pullback-stable-function-class-Prop l P) =
  is-pullback-stable-function-class l P
pr2 (is-pullback-stable-function-class-Prop l P) =
  is-prop-is-pullback-stable-function-class l P
```

## Properties

### Having equivalences is equivalent to having identity maps for function classes in a fixed universe

This is a consequence of [univalence](foundation.univalence.md).

```agda
module _
  {l1 l2 : Level} (P : function-class l1 l1 l2)
  where

  has-identity-maps-has-equivalences-function-class :
    has-equivalences-function-class P → has-identity-maps-function-class P
  has-identity-maps-has-equivalences-function-class has-equivs-P A =
    has-equivs-P A A id is-equiv-id

  htpy-has-identity-maps-function-class :
    has-identity-maps-function-class P →
    {X Y : UU l1} (p : X ＝ Y) → is-in-function-class P (map-eq p)
  htpy-has-identity-maps-function-class has-ids-P {X} refl = has-ids-P X

  has-equivalence-has-identity-maps-function-class :
    has-identity-maps-function-class P →
    {X Y : UU l1} (e : X ≃ Y) → is-in-function-class P (map-equiv e)
  has-equivalence-has-identity-maps-function-class has-ids-P {X} {Y} e =
    tr
      ( is-in-function-class P)
      ( ap pr1 (is-section-eq-equiv e))
      ( htpy-has-identity-maps-function-class has-ids-P (eq-equiv X Y e))

  has-equivalences-has-identity-maps-function-class :
    has-identity-maps-function-class P → has-equivalences-function-class P
  has-equivalences-has-identity-maps-function-class has-ids-P A B f is-equiv-f =
    has-equivalence-has-identity-maps-function-class has-ids-P (f , is-equiv-f)

  is-equiv-has-identity-maps-has-equivalences-function-class :
    is-equiv has-identity-maps-has-equivalences-function-class
  is-equiv-has-identity-maps-has-equivalences-function-class =
    is-equiv-is-prop
      ( is-prop-has-equivalences-function-class P)
      ( is-prop-has-identity-maps-function-class P)
      ( has-equivalences-has-identity-maps-function-class)

  equiv-has-identity-maps-has-equivalences-function-class :
    has-equivalences-function-class P ≃ has-identity-maps-function-class P
  pr1 equiv-has-identity-maps-has-equivalences-function-class =
    has-identity-maps-has-equivalences-function-class
  pr2 equiv-has-identity-maps-has-equivalences-function-class =
    is-equiv-has-identity-maps-has-equivalences-function-class

  is-equiv-has-equivalences-has-identity-maps-function-class :
    is-equiv has-equivalences-has-identity-maps-function-class
  is-equiv-has-equivalences-has-identity-maps-function-class =
    is-equiv-is-prop
      ( is-prop-has-identity-maps-function-class P)
      ( is-prop-has-equivalences-function-class P)
      ( has-identity-maps-has-equivalences-function-class)

  equiv-has-equivalences-has-identity-maps-function-class :
    has-identity-maps-function-class P ≃ has-equivalences-function-class P
  pr1 equiv-has-equivalences-has-identity-maps-function-class =
    has-equivalences-has-identity-maps-function-class
  pr2 equiv-has-equivalences-has-identity-maps-function-class =
    is-equiv-has-equivalences-has-identity-maps-function-class
```

### Function classes are closed under composition with equivalences

This is also a consequence of univalence.

```agda
module _
  {l1 l2 l3 : Level} (P : function-class l1 l2 l3) {A : UU l1} {B : UU l2}
  where

  is-closed-under-precomp-equiv-function-class :
    {C : UU l1} (e : A ≃ C) →
    (f : A → B) → is-in-subtype P f → is-in-subtype P (f ∘ map-inv-equiv e)
  is-closed-under-precomp-equiv-function-class e f x =
    ind-equiv (λ _ x → is-in-subtype P (f ∘ map-inv-equiv x)) x e

  is-closed-under-postcomp-equiv-function-class :
    {D : UU l2} (e : B ≃ D) →
    (f : A → B) → is-in-subtype P f → is-in-subtype P (map-equiv e ∘ f)
  is-closed-under-postcomp-equiv-function-class e f x =
    ind-equiv (λ _ x → is-in-subtype P (map-equiv x ∘ f)) x e
```
