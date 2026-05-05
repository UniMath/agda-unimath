# Equivalences

```agda
module foundation.equivalences where

open import foundation-core.equivalences public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equivalence-extensionality
open import foundation.equivalences-contractible-types
open import foundation.function-extensionality
open import foundation.functoriality-fibers-of-maps
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.transposition-identifications-along-equivalences
open import foundation.truncated-maps
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.retractions
open import foundation-core.retracts-of-types
open import foundation-core.sections
open import foundation-core.subtypes
open import foundation-core.truncation-levels
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Properties

### Any equivalence is an embedding

We already proved in `foundation-core.equivalences` that equivalences are
embeddings. Here we have `_↪_` available, so we record the map from equivalences
to embeddings.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb-equiv : (e : A ≃ B) → is-emb (map-equiv e)
  is-emb-equiv e = is-emb-is-equiv (is-equiv-map-equiv e)

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = map-equiv e
  pr2 (emb-equiv e) = is-emb-equiv e
```

### Equivalences have a contractible type of sections

**Proof:** Since equivalences are
[contractible maps](foundation.contractible-maps.md), and products of
[contractible types](foundation-core.contractible-types.md) are contractible, it
follows that the type

```text
  (b : B) → fiber f b
```

is contractible, for any equivalence `f`. However, by the
[type theoretic principle of choice](foundation.type-theoretic-principle-of-choice.md)
it follows that this type is equivalent to the type

```text
  Σ (B → A) (λ g → (b : B) → f (g b) ＝ b),
```

which is the type of [sections](foundation.sections.md) of `f`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-section-is-equiv : {f : A → B} → is-equiv f → is-contr (section f)
    is-contr-section-is-equiv {f} is-equiv-f =
      is-contr-equiv'
        ( (b : B) → fiber f b)
        ( distributive-Π-Σ)
        ( is-contr-Π (is-contr-map-is-equiv is-equiv-f))
```

### Equivalences have a contractible type of retractions

**Proof:** Since precomposing by an equivalence is an equivalence, and
equivalences are contractible maps, it follows that the
[fiber](foundation-core.fibers-of-maps.md) of the map

```text
  (B → A) → (A → A)
```

at `id : A → A` is contractible, i.e., the type `Σ (B → A) (λ h → h ∘ f ＝ id)`
is contractible. Furthermore, since fiberwise equivalences induce equivalences
on total spaces, it follows from
[function extensionality](foundation.function-extensionality.md) that the type

```text
  Σ (B → A) (λ h → h ∘ f ~ id)
```

is contractible. In other words, the type of retractions of an equivalence is
contractible.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-retraction-is-equiv :
      {f : A → B} → is-equiv f → is-contr (retraction f)
    is-contr-retraction-is-equiv {f} is-equiv-f =
      is-contr-equiv'
        ( Σ (B → A) (λ h → h ∘ f ＝ id))
        ( equiv-tot (λ h → equiv-funext))
        ( is-contr-map-is-equiv (is-equiv-precomp-is-equiv f is-equiv-f A) id)
```

### The underlying retract of an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  retract-equiv : A ≃ B → A retract-of B
  retract-equiv e =
    ( map-equiv e , map-inv-equiv e , is-retraction-map-inv-equiv e)

  retract-inv-equiv : B ≃ A → A retract-of B
  retract-inv-equiv e =
    ( map-inv-equiv e , map-equiv e , is-section-map-inv-equiv e)
```

### Being an equivalence is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-is-equiv-is-equiv : {f : A → B} → is-equiv f → is-contr (is-equiv f)
  is-contr-is-equiv-is-equiv is-equiv-f =
    is-contr-product
      ( is-contr-section-is-equiv is-equiv-f)
      ( is-contr-retraction-is-equiv is-equiv-f)

  abstract
    is-property-is-equiv : (f : A → B) → (H K : is-equiv f) → is-contr (H ＝ K)
    is-property-is-equiv f H =
      is-prop-is-contr (is-contr-is-equiv-is-equiv H) H

  is-equiv-Prop : (f : A → B) → Prop (l1 ⊔ l2)
  pr1 (is-equiv-Prop f) = is-equiv f
  pr2 (is-equiv-Prop f) = is-property-is-equiv f

  eq-equiv-eq-map-equiv :
    {e e' : A ≃ B} → (map-equiv e) ＝ (map-equiv e') → e ＝ e'
  eq-equiv-eq-map-equiv = eq-type-subtype is-equiv-Prop

  abstract
    is-emb-map-equiv :
      is-emb (map-equiv {A = A} {B = B})
    is-emb-map-equiv = is-emb-inclusion-subtype is-equiv-Prop

  is-injective-map-equiv :
    is-injective (map-equiv {A = A} {B = B})
  is-injective-map-equiv = is-injective-is-emb is-emb-map-equiv

  emb-map-equiv : (A ≃ B) ↪ (A → B)
  pr1 emb-map-equiv = map-equiv
  pr2 emb-map-equiv = is-emb-map-equiv
```

### The 3-for-2 property of being an equivalence

#### If the right factor is an equivalence, then the left factor being an equivalence is equivalent to the composite being one

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-is-equiv-right-map-triangle :
    { f : A → B} (e : B ≃ C) (h : A → C)
    ( H : coherence-triangle-maps h (map-equiv e) f) →
    is-equiv f ≃ is-equiv h
  equiv-is-equiv-right-map-triangle {f} e h H =
    equiv-iff-is-prop
      ( is-property-is-equiv f)
      ( is-property-is-equiv h)
      ( λ is-equiv-f →
        is-equiv-left-map-triangle h (map-equiv e) f H is-equiv-f
          ( is-equiv-map-equiv e))
      ( is-equiv-top-map-triangle h (map-equiv e) f H (is-equiv-map-equiv e))

  equiv-is-equiv-left-factor :
    { f : A → B} (e : B ≃ C) →
    is-equiv f ≃ is-equiv (map-equiv e ∘ f)
  equiv-is-equiv-left-factor {f} e =
    equiv-is-equiv-right-map-triangle e (map-equiv e ∘ f) refl-htpy
```

#### If the left factor is an equivalence, then the right factor being an equivalence is equivalent to the composite being one

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-is-equiv-top-map-triangle :
    ( e : A ≃ B) {f : B → C} (h : A → C)
    ( H : coherence-triangle-maps h f (map-equiv e)) →
    is-equiv f ≃ is-equiv h
  equiv-is-equiv-top-map-triangle e {f} h H =
    equiv-iff-is-prop
      ( is-property-is-equiv f)
      ( is-property-is-equiv h)
      ( is-equiv-left-map-triangle h f (map-equiv e) H (is-equiv-map-equiv e))
      ( λ is-equiv-h →
        is-equiv-right-map-triangle h f
          ( map-equiv e)
          ( H)
          ( is-equiv-h)
          ( is-equiv-map-equiv e))

  equiv-is-equiv-right-factor :
    ( e : A ≃ B) {f : B → C} →
    is-equiv f ≃ is-equiv (f ∘ map-equiv e)
  equiv-is-equiv-right-factor e {f} =
    equiv-is-equiv-top-map-triangle e (f ∘ map-equiv e) refl-htpy
```

### The 6-for-2 property of equivalences

Consider a commuting diagram of maps

```text
         i
    A ------> X
    |       ∧ |
  f |     /   | g
    |   h     |
    ∨ /       ∨
    B ------> Y.
         j
```

The **6-for-2 property of equivalences** asserts that if `i` and `j` are
equivalences, then so are `h`, `f`, `g`, and the triple composite `g ∘ h ∘ f`.
The 6-for-2 property is also commonly known as the **2-out-of-6 property**.

**First proof:** Since `i` is an equivalence, it follows that `i` is surjective.
This implies that `h` is surjective. Furthermore, since `j` is an equivalence it
follows that `j` is an embedding. This implies that `h` is an embedding. The map
`h` is therefore both surjective and an embedding, so it must be an equivalence.
The fact that `f` and `g` are equivalences now follows from a simple application
of the 3-for-2 property of equivalences.

Unfortunately, the above proof requires us to import `surjective-maps`, which
causes a cyclic module dependency. We therefore give a second proof, which
avoids the fact that maps that are both surjective and an embedding are
equivalences.

**Second proof:** By reasoning similar to that in the first proof, it suffices
to show that the diagonal filler `h` is an equivalence. The map `f ∘ i⁻¹` is a
section of `h`, since we have `(h ∘ f ~ i) → (h ∘ f ∘ i⁻¹ ~ id)` by transposing
along equivalences. Similarly, the map `j⁻¹ ∘ g` is a retraction of `h`, since
we have `(g ∘ h ~ j) → (j⁻¹ ∘ g ∘ h ~ id)` by transposing along equivalences.
Since `h` therefore has a section and a retraction, it is an equivalence.

In fact, the above argument shows that if the top map `i` has a section and the
bottom map `j` has a retraction, then the diagonal filler, and hence all other
maps are equivalences.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) {i : A → X} {j : B → Y} (h : B → X)
  (u : coherence-triangle-maps i h f) (v : coherence-triangle-maps j g h)
  where

  section-diagonal-filler-section-top-square :
    section i → section h
  section-diagonal-filler-section-top-square =
    section-right-map-triangle i h f u

  section-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → section h
  section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H =
    section-diagonal-filler-section-top-square (section-is-equiv H)

  map-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → X → B
  map-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H =
    map-section h
      ( section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H)

  is-section-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    (H : is-equiv i) →
    is-section h
      ( map-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H)
  is-section-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H =
    is-section-map-section h
      ( section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H)

  retraction-diagonal-filler-retraction-bottom-square :
    retraction j → retraction h
  retraction-diagonal-filler-retraction-bottom-square =
    retraction-top-map-triangle j g h v

  retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv j → retraction h
  retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square K =
    retraction-diagonal-filler-retraction-bottom-square (retraction-is-equiv K)

  map-retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv j → X → B
  map-retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square K =
    map-retraction h
      ( retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square K)

  is-retraction-retraction-diagonal-fller-is-equiv-top-is-equiv-bottom-square :
    (K : is-equiv j) →
    is-retraction h
      ( map-retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square K)
  is-retraction-retraction-diagonal-fller-is-equiv-top-is-equiv-bottom-square
    K =
    is-retraction-map-retraction h
      ( retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square K)

  is-equiv-diagonal-filler-section-top-retraction-bottom-square :
    section i → retraction j → is-equiv h
  pr1 (is-equiv-diagonal-filler-section-top-retraction-bottom-square H K) =
    section-diagonal-filler-section-top-square H
  pr2 (is-equiv-diagonal-filler-section-top-retraction-bottom-square H K) =
    retraction-diagonal-filler-retraction-bottom-square K

  is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → is-equiv j → is-equiv h
  is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-square H K =
    is-equiv-diagonal-filler-section-top-retraction-bottom-square
      ( section-is-equiv H)
      ( retraction-is-equiv K)

  is-equiv-left-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → is-equiv j → is-equiv f
  is-equiv-left-is-equiv-top-is-equiv-bottom-square H K =
    is-equiv-top-map-triangle i h f u
      ( is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-square H K)
      ( H)

  is-equiv-right-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → is-equiv j → is-equiv g
  is-equiv-right-is-equiv-top-is-equiv-bottom-square H K =
    is-equiv-right-map-triangle j g h v K
      ( is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-square H K)

  is-equiv-triple-comp :
    is-equiv i → is-equiv j → is-equiv (g ∘ h ∘ f)
  is-equiv-triple-comp H K =
    is-equiv-comp g
      ( h ∘ f)
      ( is-equiv-comp h f
        ( is-equiv-left-is-equiv-top-is-equiv-bottom-square H K)
        ( is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-square H K))
      ( is-equiv-right-is-equiv-top-is-equiv-bottom-square H K)
```

### Being an equivalence is closed under homotopies

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-is-equiv-htpy :
    { f g : A → B} → (f ~ g) →
    is-equiv f ≃ is-equiv g
  equiv-is-equiv-htpy {f} {g} H =
    equiv-iff-is-prop
      ( is-property-is-equiv f)
      ( is-property-is-equiv g)
      ( is-equiv-htpy f (inv-htpy H))
      ( is-equiv-htpy g H)
```

### The groupoid laws for equivalences

#### Composition of equivalences is associative

```agda
associative-comp-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (e : A ≃ B) (f : B ≃ C) (g : C ≃ D) →
  ((g ∘e f) ∘e e) ＝ (g ∘e (f ∘e e))
associative-comp-equiv e f g = eq-equiv-eq-map-equiv refl
```

#### Unit laws for composition of equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  left-unit-law-equiv : (e : X ≃ Y) → (id-equiv ∘e e) ＝ e
  left-unit-law-equiv e = eq-equiv-eq-map-equiv refl

  right-unit-law-equiv : (e : X ≃ Y) → (e ∘e id-equiv) ＝ e
  right-unit-law-equiv e = eq-equiv-eq-map-equiv refl
```

#### A coherence law for the unit laws for composition of equivalences

```agda
coh-unit-laws-equiv :
  {l : Level} {X : UU l} →
  left-unit-law-equiv (id-equiv {A = X}) ＝
  right-unit-law-equiv (id-equiv {A = X})
coh-unit-laws-equiv = ap eq-equiv-eq-map-equiv refl
```

#### Inverse laws for composition of equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  left-inverse-law-equiv : (e : X ≃ Y) → ((inv-equiv e) ∘e e) ＝ id-equiv
  left-inverse-law-equiv e =
    eq-htpy-equiv (is-retraction-map-inv-is-equiv (is-equiv-map-equiv e))

  right-inverse-law-equiv : (e : X ≃ Y) → (e ∘e (inv-equiv e)) ＝ id-equiv
  right-inverse-law-equiv e =
    eq-htpy-equiv (is-section-map-inv-is-equiv (is-equiv-map-equiv e))
```

#### `inv-equiv` is a fibered involution on equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  inv-inv-equiv : (e : X ≃ Y) → (inv-equiv (inv-equiv e)) ＝ e
  inv-inv-equiv e = eq-equiv-eq-map-equiv refl

  inv-inv-equiv' : (e : Y ≃ X) → (inv-equiv (inv-equiv e)) ＝ e
  inv-inv-equiv' e = eq-equiv-eq-map-equiv refl

  is-equiv-inv-equiv : is-equiv (inv-equiv {A = X} {B = Y})
  is-equiv-inv-equiv =
    is-equiv-is-invertible
      ( inv-equiv)
      ( inv-inv-equiv')
      ( inv-inv-equiv)

  equiv-inv-equiv : (X ≃ Y) ≃ (Y ≃ X)
  pr1 equiv-inv-equiv = inv-equiv
  pr2 equiv-inv-equiv = is-equiv-inv-equiv
```

#### Taking the inverse equivalence distributes over composition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3}
  where

  distributive-inv-comp-equiv :
    (e : X ≃ Y) (f : Y ≃ Z) →
    inv-equiv (f ∘e e) ＝ (inv-equiv e) ∘e (inv-equiv f)
  distributive-inv-comp-equiv e f =
    eq-htpy-equiv
      ( λ x →
        map-eq-transpose-equiv-inv
          ( f ∘e e)
          ( ( ap (λ g → map-equiv g x) (inv (right-inverse-law-equiv f))) ∙
            ( ap
              ( λ g → map-equiv (f ∘e (g ∘e (inv-equiv f))) x)
              ( inv (right-inverse-law-equiv e)))))

  distributive-map-inv-comp-equiv :
    (e : X ≃ Y) (f : Y ≃ Z) →
    map-inv-equiv (f ∘e e) ＝ map-inv-equiv e ∘ map-inv-equiv f
  distributive-map-inv-comp-equiv e f =
    ap map-equiv (distributive-inv-comp-equiv e f)
```

### Postcomposition of equivalences by an equivalence is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-retraction-postcomp-equiv-inv-equiv :
    (f : B ≃ C) (e : A ≃ B) → inv-equiv f ∘e (f ∘e e) ＝ e
  is-retraction-postcomp-equiv-inv-equiv f e =
    eq-htpy-equiv (λ x → is-retraction-map-inv-equiv f (map-equiv e x))

  is-section-postcomp-equiv-inv-equiv :
    (f : B ≃ C) (e : A ≃ C) → f ∘e (inv-equiv f ∘e e) ＝ e
  is-section-postcomp-equiv-inv-equiv f e =
    eq-htpy-equiv (λ x → is-section-map-inv-equiv f (map-equiv e x))

  is-equiv-postcomp-equiv-equiv :
    (f : B ≃ C) → is-equiv (λ (e : A ≃ B) → f ∘e e)
  is-equiv-postcomp-equiv-equiv f =
    is-equiv-is-invertible
      ( inv-equiv f ∘e_)
      ( is-section-postcomp-equiv-inv-equiv f)
      ( is-retraction-postcomp-equiv-inv-equiv f)

equiv-postcomp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3} →
  (f : B ≃ C) → (A : UU l1) → (A ≃ B) ≃ (A ≃ C)
pr1 (equiv-postcomp-equiv f A) = f ∘e_
pr2 (equiv-postcomp-equiv f A) = is-equiv-postcomp-equiv-equiv f
```

### Precomposition of equivalences by an equivalence is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-retraction-precomp-equiv-inv-equiv :
    (e : A ≃ B) (f : B ≃ C) → (f ∘e e) ∘e inv-equiv e ＝ f
  is-retraction-precomp-equiv-inv-equiv e f =
    eq-htpy-equiv (λ x → ap (map-equiv f) (is-section-map-inv-equiv e x))

  is-section-precomp-equiv-inv-equiv :
    (e : A ≃ B) (f : A ≃ C) → (f ∘e inv-equiv e) ∘e e ＝ f
  is-section-precomp-equiv-inv-equiv e f =
    eq-htpy-equiv (λ x → ap (map-equiv f) (is-retraction-map-inv-equiv e x))

  is-equiv-precomp-equiv-equiv :
    (e : A ≃ B) → is-equiv (λ (f : B ≃ C) → f ∘e e)
  is-equiv-precomp-equiv-equiv e =
    is-equiv-is-invertible
      ( _∘e inv-equiv e)
      ( is-section-precomp-equiv-inv-equiv e)
      ( is-retraction-precomp-equiv-inv-equiv e)

equiv-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
pr1 (equiv-precomp-equiv e C) = _∘e e
pr2 (equiv-precomp-equiv e C) = is-equiv-precomp-equiv-equiv e
```

### Transposing inverses

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3}
  (p : X ≃ Y) (q : Y ≃ Z) (r : X ≃ Z)
  where

  equiv-right-transpose-equiv-comp :
    (q ∘e p ＝ r) ≃ (q ＝ r ∘e inv-equiv p)
  equiv-right-transpose-equiv-comp =
    eq-transpose-equiv (equiv-precomp-equiv p Z) q r

  equiv-left-transpose-equiv-comp :
    (q ∘e p ＝ r) ≃ (p ＝ inv-equiv q ∘e r)
  equiv-left-transpose-equiv-comp =
    eq-transpose-equiv (equiv-postcomp-equiv q X) p r

  right-transpose-equiv-comp :
    q ∘e p ＝ r → q ＝ r ∘e inv-equiv p
  right-transpose-equiv-comp s =
    inv (is-retraction-precomp-equiv-inv-equiv p q) ∙ ap (_∘e inv-equiv p) s

  inv-right-transpose-equiv-comp :
    q ＝ r ∘e inv-equiv p → q ∘e p ＝ r
  inv-right-transpose-equiv-comp s =
    ap (_∘e p) s ∙ is-section-precomp-equiv-inv-equiv p r

  left-transpose-equiv-comp :
    q ∘e p ＝ r → p ＝ inv-equiv q ∘e r
  left-transpose-equiv-comp s =
    inv (is-retraction-postcomp-equiv-inv-equiv q p) ∙ ap (inv-equiv q ∘e_) s

  inv-left-transpose-equiv-comp :
    p ＝ inv-equiv q ∘e r → q ∘e p ＝ r
  inv-left-transpose-equiv-comp s =
    ap (q ∘e_) s ∙ is-section-postcomp-equiv-inv-equiv q r
```

### Computing transport in the type of equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  where

  tr-equiv-type :
    {x y : A} (p : x ＝ y) (e : B x ≃ C x) →
    tr (λ x → B x ≃ C x) p e ＝ equiv-tr C p ∘e e ∘e equiv-tr B (inv p)
  tr-equiv-type refl e = eq-htpy-equiv refl-htpy

module _
  {l1 l2 : Level} {X : UU l1} {Y Y' : UU l2}
  where

  tr-equiv-type-right :
    (p : Y ＝ Y') (α : X ≃ Y) → equiv-tr id p ∘e α ＝ tr (X ≃_) p α
  tr-equiv-type-right refl = left-unit-law-equiv

  tr-equiv-type-left :
    (p : Y ＝ Y') (α : Y ≃ X) → α ∘e equiv-tr id (inv p) ＝ tr (_≃ X) p α
  tr-equiv-type-left refl = right-unit-law-equiv
```

### A cospan in which one of the legs is an equivalence is a pullback if and only if the corresponding map on the cone is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-equiv-vertical-map-is-pullback :
      is-equiv g → is-pullback f g c → is-equiv (vertical-map-cone f g c)
    is-equiv-vertical-map-is-pullback is-equiv-g pb =
      is-equiv-is-contr-map
        ( is-trunc-vertical-map-is-pullback neg-two-𝕋 f g c pb
          ( is-contr-map-is-equiv is-equiv-g))

  abstract
    is-pullback-is-equiv-vertical-maps :
      is-equiv g → is-equiv (vertical-map-cone f g c) → is-pullback f g c
    is-pullback-is-equiv-vertical-maps is-equiv-g is-equiv-p =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone f g c
        ( λ a →
          is-equiv-is-contr
            ( map-fiber-vertical-map-cone f g c a)
            ( is-contr-map-is-equiv is-equiv-p a)
            ( is-contr-map-is-equiv is-equiv-g (f a)))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-equiv-horizontal-map-is-pullback :
      is-equiv f → is-pullback f g c → is-equiv (horizontal-map-cone f g c)
    is-equiv-horizontal-map-is-pullback is-equiv-f pb =
      is-equiv-is-contr-map
        ( is-trunc-horizontal-map-is-pullback neg-two-𝕋 f g c pb
          ( is-contr-map-is-equiv is-equiv-f))

  abstract
    is-pullback-is-equiv-horizontal-maps :
      is-equiv f → is-equiv (horizontal-map-cone f g c) → is-pullback f g c
    is-pullback-is-equiv-horizontal-maps is-equiv-f is-equiv-q =
      is-pullback-swap-cone' f g c
        ( is-pullback-is-equiv-vertical-maps g f
          ( swap-cone f g c)
          ( is-equiv-f)
          ( is-equiv-q))
```

## See also

- For the notion of coherently invertible maps, also known as half-adjoint
  equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
- For the notion of finitely coherent equivalence, see
  [`foundation.finitely-coherent-equivalence`)(foundation.finitely-coherent-equivalence.md).
- For the notion of finitely coherently invertible map, see
  [`foundation.finitely-coherently-invertible-map`)(foundation.finitely-coherently-invertible-map.md).
- For the notion of infinitely coherent equivalence, see
  [`foundation.infinitely-coherent-equivalences`](foundation.infinitely-coherent-equivalences.md).

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}

## External links

- The
  [2-out-of-6 property](https://ncatlab.org/nlab/show/two-out-of-six+property)
  at $n$Lab
