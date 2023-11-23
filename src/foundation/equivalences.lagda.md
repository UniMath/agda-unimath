# Equivalences

```agda
module foundation.equivalences where

open import foundation-core.equivalences public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.functoriality-fibers-of-maps
open import foundation.identity-types
open import foundation.truncated-maps
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.subtypes
open import foundation-core.truncation-levels
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

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = map-equiv e
  pr2 (emb-equiv e) = is-emb-is-equiv (is-equiv-map-equiv e)
```

### Transposing equalities along equivalences

The fact that equivalences are embeddings has many important consequences, we
will use some of these consequences in order to derive basic properties of
embeddings.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv :
    (x : A) (y : B) → (map-equiv e x ＝ y) ≃ (x ＝ map-inv-equiv e y)
  eq-transpose-equiv x y =
    ( inv-equiv (equiv-ap e x (map-inv-equiv e y))) ∘e
    ( equiv-concat'
      ( map-equiv e x)
      ( inv (is-section-map-inv-equiv e y)))

  map-eq-transpose-equiv :
    {x : A} {y : B} → map-equiv e x ＝ y → x ＝ map-inv-equiv e y
  map-eq-transpose-equiv {x} {y} = map-equiv (eq-transpose-equiv x y)

  inv-map-eq-transpose-equiv :
    {x : A} {y : B} → x ＝ map-inv-equiv e y → map-equiv e x ＝ y
  inv-map-eq-transpose-equiv {x} {y} = map-inv-equiv (eq-transpose-equiv x y)

  triangle-eq-transpose-equiv :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    ( ( ap (map-equiv e) (map-eq-transpose-equiv p)) ∙
      ( is-section-map-inv-equiv e y)) ＝
    ( p)
  triangle-eq-transpose-equiv {x} {y} p =
    ( ap
      ( concat' (map-equiv e x) (is-section-map-inv-equiv e y))
      ( is-section-map-inv-equiv
        ( equiv-ap e x (map-inv-equiv e y))
        ( p ∙ inv (is-section-map-inv-equiv e y)))) ∙
    ( ( assoc
        ( p)
        ( inv (is-section-map-inv-equiv e y))
        ( is-section-map-inv-equiv e y)) ∙
      ( ( ap (concat p y) (left-inv (is-section-map-inv-equiv e y))) ∙
        ( right-unit)))

  map-eq-transpose-equiv' :
    {a : A} {b : B} → b ＝ map-equiv e a → map-inv-equiv e b ＝ a
  map-eq-transpose-equiv' p = inv (map-eq-transpose-equiv (inv p))

  inv-map-eq-transpose-equiv' :
    {a : A} {b : B} → map-inv-equiv e b ＝ a → b ＝ map-equiv e a
  inv-map-eq-transpose-equiv' p =
    inv (inv-map-eq-transpose-equiv (inv p))

  triangle-eq-transpose-equiv' :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( (is-section-map-inv-equiv e y) ∙ p) ＝
    ( ap (map-equiv e) (map-eq-transpose-equiv' p))
  triangle-eq-transpose-equiv' {x} {y} p =
    map-inv-equiv
      ( equiv-ap
        ( equiv-inv (map-equiv e (map-inv-equiv e y)) (map-equiv e x))
        ( (is-section-map-inv-equiv e y) ∙ p)
        ( ap (map-equiv e) (map-eq-transpose-equiv' p)))
      ( ( distributive-inv-concat (is-section-map-inv-equiv e y) p) ∙
        ( ( inv
            ( right-transpose-eq-concat
              ( ap (map-equiv e) (inv (map-eq-transpose-equiv' p)))
              ( is-section-map-inv-equiv e y)
              ( inv p)
              ( ( ap
                  ( concat' (map-equiv e x) (is-section-map-inv-equiv e y))
                  ( ap
                    ( ap (map-equiv e))
                    ( inv-inv
                      ( map-inv-equiv
                        ( equiv-ap e x (map-inv-equiv e y))
                        ( ( inv p) ∙
                          ( inv (is-section-map-inv-equiv e y))))))) ∙
                ( triangle-eq-transpose-equiv (inv p))))) ∙
          ( ap-inv (map-equiv e) (map-eq-transpose-equiv' p))))
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
[function extensionality](foundation.function-extensionality.md)` that the type

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

### Being an equivalence is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-is-equiv-is-equiv : {f : A → B} → is-equiv f → is-contr (is-equiv f)
  is-contr-is-equiv-is-equiv is-equiv-f =
    is-contr-prod
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
    equiv-prop
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
    equiv-prop
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
    A ---> X
    |    ∧ |
    |   /  |
  f |  h   | g
    V /    V
    B ---> Y
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
    equiv-prop
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

#### Inverse laws for composition of equivalences

```agda
  left-inverse-law-equiv : (e : X ≃ Y) → ((inv-equiv e) ∘e e) ＝ id-equiv
  left-inverse-law-equiv e =
    eq-htpy-equiv (is-retraction-map-inv-is-equiv (is-equiv-map-equiv e))

  right-inverse-law-equiv : (e : X ≃ Y) → (e ∘e (inv-equiv e)) ＝ id-equiv
  right-inverse-law-equiv e =
    eq-htpy-equiv (is-section-map-inv-is-equiv (is-equiv-map-equiv e))
```

#### `inv-equiv` is a fibered involution on equivalences

```agda
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

#### A coherence law for the unit laws for composition of equivalences

```agda
coh-unit-laws-equiv :
  {l : Level} {X : UU l} →
  left-unit-law-equiv (id-equiv {A = X}) ＝
  right-unit-law-equiv (id-equiv {A = X})
coh-unit-laws-equiv = ap eq-equiv-eq-map-equiv refl
```

#### Taking the inverse equivalence distributes over composition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3}
  where

  distributive-inv-comp-equiv :
    (e : X ≃ Y) (f : Y ≃ Z) →
    (inv-equiv (f ∘e e)) ＝ ((inv-equiv e) ∘e (inv-equiv f))
  distributive-inv-comp-equiv e f =
    eq-htpy-equiv
      ( λ x →
        map-eq-transpose-equiv'
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

#### Iterated inverse laws for equivalence composition

```agda
is-retraction-postcomp-equiv-inv-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ B) → (inv-equiv f ∘e (f ∘e e)) ＝ e
is-retraction-postcomp-equiv-inv-equiv f e =
  eq-htpy-equiv (λ x → is-retraction-map-inv-equiv f (map-equiv e x))

is-section-postcomp-equiv-inv-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ C) →
  (f ∘e (inv-equiv f ∘e e)) ＝ e
is-section-postcomp-equiv-inv-equiv f e =
  eq-htpy-equiv (λ x → is-section-map-inv-equiv f (map-equiv e x))

is-section-precomp-equiv-inv-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ B) →
  ((f ∘e e) ∘e inv-equiv e) ＝ f
is-section-precomp-equiv-inv-equiv f e =
  eq-htpy-equiv (λ x → ap (map-equiv f) (is-section-map-inv-equiv e x))

is-retraction-precomp-equiv-inv-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : B ≃ A) →
  ((f ∘e inv-equiv e) ∘e e) ＝ f
is-retraction-precomp-equiv-inv-equiv f e =
  eq-htpy-equiv (λ x → ap (map-equiv f) (is-retraction-map-inv-equiv e x))
```

### The post- and precomposition operations by an equivalence are equivalences

```agda
is-equiv-postcomp-equiv-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (A : UU l1) → is-equiv (λ (e : A ≃ B) → f ∘e e)
is-equiv-postcomp-equiv-equiv f A =
  is-equiv-is-invertible
    ( inv-equiv f ∘e_)
    ( is-section-postcomp-equiv-inv-equiv f)
    ( is-retraction-postcomp-equiv-inv-equiv f)

is-equiv-precomp-equiv-equiv :
  {l1 l2 l3 : Level} {A : UU l2} {B : UU l3}
  (C : UU l1) (e : A ≃ B) → is-equiv (λ (f : B ≃ C) → f ∘e e)
is-equiv-precomp-equiv-equiv A e =
  is-equiv-is-invertible
    ( _∘e inv-equiv e)
    ( λ f → is-retraction-precomp-equiv-inv-equiv f e)
    ( λ f → is-section-precomp-equiv-inv-equiv f e)

equiv-postcomp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3} →
  (f : B ≃ C) → (A : UU l1) → (A ≃ B) ≃ (A ≃ C)
pr1 (equiv-postcomp-equiv f A) = f ∘e_
pr2 (equiv-postcomp-equiv f A) = is-equiv-postcomp-equiv-equiv f A
```

```agda
equiv-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
pr1 (equiv-precomp-equiv e C) = _∘e e
pr2 (equiv-precomp-equiv e C) = is-equiv-precomp-equiv-equiv C e
```

### A cospan in which one of the legs is an equivalence is a pullback if and only if the corresponding map on the cone is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-equiv-is-pullback : is-equiv g → is-pullback f g c → is-equiv (pr1 c)
    is-equiv-is-pullback is-equiv-g pb =
      is-equiv-is-contr-map
        ( is-trunc-is-pullback neg-two-𝕋 f g c pb
          ( is-contr-map-is-equiv is-equiv-g))

  abstract
    is-pullback-is-equiv : is-equiv g → is-equiv (pr1 c) → is-pullback f g c
    is-pullback-is-equiv is-equiv-g is-equiv-p =
      is-pullback-is-fiberwise-equiv-map-fiber-cone f g c
        ( λ a → is-equiv-is-contr
          ( map-fiber-cone f g c a)
          ( is-contr-map-is-equiv is-equiv-p a)
          ( is-contr-map-is-equiv is-equiv-g (f a)))
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-equiv-is-pullback' :
      is-equiv f → is-pullback f g c → is-equiv (pr1 (pr2 c))
    is-equiv-is-pullback' is-equiv-f pb =
      is-equiv-is-contr-map
        ( is-trunc-is-pullback' neg-two-𝕋 f g c pb
          ( is-contr-map-is-equiv is-equiv-f))

  abstract
    is-pullback-is-equiv' :
      is-equiv f → is-equiv (pr1 (pr2 c)) → is-pullback f g c
    is-pullback-is-equiv' is-equiv-f is-equiv-q =
      is-pullback-swap-cone' f g c
        ( is-pullback-is-equiv g f
          ( swap-cone f g c)
          is-equiv-f
          is-equiv-q)
```

### Families of equivalences are equivalent to fiberwise equivalences

```agda
equiv-fiberwise-equiv-fam-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  fam-equiv B C ≃ fiberwise-equiv B C
equiv-fiberwise-equiv-fam-equiv B C = distributive-Π-Σ
```

## See also

- For the notions of inverses and coherently invertible maps, also known as
  half-adjoint equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).

## External links

- The
  [2-out-of-6 property](https://ncatlab.org/nlab/show/two-out-of-six+property)
  at $n$Lab
