# Local types

```agda
module orthogonal-factorization-systems.types-local-at-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.empty-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.retracts-of-maps
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels
```

</details>

## Idea

A dependent type `A` over `Y` is said to be
{{#concept "local at" Disambiguation="map of types"}} `f : X → Y`, or
{{#concept "`f`-local" Disambiguation="map of types"}} , if the
[precomposition map](foundation-core.function-types.md)

```text
  _∘ f : ((y : Y) → A y) → ((x : X) → A (f x))
```

is an [equivalence](foundation-core.equivalences.md).

We reserve the name `is-local` for when `A` does not vary over `Y`, and specify
with `is-local-dependent-type` when it does.

Note that a local dependent type is not the same as a
[local family](orthogonal-factorization-systems.families-of-types-local-at-maps.md).
While a local family is a type family `P` on some other indexing type `A`, such
that each fiber is local as a nondependent type over `Y`, a local dependent type
is a local type that additionally may vary over `Y`. Concretely, a local
dependent type `A` may be understood as a family of types such that for every
`y : Y`, `A y` is
`fiber f y`-[null](orthogonal-factorization-systems.null-types.md).

## Definition

### Local dependent types

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) (A : Y → UU l3)
  where

  is-local-dependent-type : UU (l1 ⊔ l2 ⊔ l3)
  is-local-dependent-type = is-equiv (precomp-Π f A)

  is-property-is-local-dependent-type : is-prop is-local-dependent-type
  is-property-is-local-dependent-type = is-property-is-equiv (precomp-Π f A)

  is-local-dependent-type-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 is-local-dependent-type-Prop = is-local-dependent-type
  pr2 is-local-dependent-type-Prop = is-property-is-local-dependent-type
```

### Local types

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) (A : UU l3)
  where

  is-local : UU (l1 ⊔ l2 ⊔ l3)
  is-local = is-local-dependent-type f (λ _ → A)

  is-property-is-local : is-prop is-local
  is-property-is-local = is-property-is-local-dependent-type f (λ _ → A)

  is-local-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  is-local-Prop = is-local-dependent-type-Prop f (λ _ → A)
```

## Properties

### Locality distributes over Π-types

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  distributive-Π-is-local-dependent-type :
    {l3 l4 : Level} {A : UU l3} (B : A → Y → UU l4) →
    ((a : A) → is-local-dependent-type f (B a)) →
    is-local-dependent-type f (λ x → (a : A) → B a x)
  distributive-Π-is-local-dependent-type B f-loc =
    is-equiv-map-equiv
      ( ( equiv-swap-Π) ∘e
        ( equiv-Π-equiv-family (λ a → precomp-Π f (B a) , (f-loc a))) ∘e
        ( equiv-swap-Π))

  distributive-Π-is-local :
    {l3 l4 : Level} {A : UU l3} (B : A → UU l4) →
    ((a : A) → is-local f (B a)) →
    is-local f ((a : A) → B a)
  distributive-Π-is-local B =
    distributive-Π-is-local-dependent-type (λ a _ → B a)
```

### Local types are closed under equivalences

```agda
module _
  {l1 l2 l3 l4 : Level}
  {X : UU l1} {Y : UU l2} {A : Y → UU l3} {B : Y → UU l4}
  (f : X → Y)
  where

  is-local-dependent-type-fam-equiv :
    fam-equiv A B → is-local-dependent-type f B → is-local-dependent-type f A
  is-local-dependent-type-fam-equiv e is-local-B =
    is-equiv-htpy-equiv
      ( ( equiv-Π-equiv-family (inv-equiv ∘ e ∘ f)) ∘e
        ( precomp-Π f B , is-local-B) ∘e
        ( equiv-Π-equiv-family e))
      ( λ g →
        eq-htpy (λ y → inv (is-retraction-map-inv-equiv (e (f y)) (g (f y)))))

  is-local-dependent-type-inv-fam-equiv :
    fam-equiv B A → is-local-dependent-type f B → is-local-dependent-type f A
  is-local-dependent-type-inv-fam-equiv e =
    is-local-dependent-type-fam-equiv (inv-equiv ∘ e)

module _
  {l1 l2 l3 l4 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4}
  (f : X → Y)
  where

  is-local-equiv : A ≃ B → is-local f B → is-local f A
  is-local-equiv e = is-local-dependent-type-fam-equiv f (λ _ → e)

  is-local-inv-equiv : B ≃ A → is-local f B → is-local f A
  is-local-inv-equiv e = is-local-dependent-type-inv-fam-equiv f (λ _ → e)
```

### Locality is preserved by homotopies

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {A : UU l3} {f f' : X → Y}
  where

  is-local-htpy : (H : f ~ f') → is-local f' A → is-local f A
  is-local-htpy H = is-equiv-htpy (precomp f' A) (htpy-precomp H A)

  is-local-htpy' : (H : f ~ f') → is-local f A → is-local f' A
  is-local-htpy' H = is-equiv-htpy' (precomp f A) (htpy-precomp H A)
```

### If `S` is `f`-local then `S` is local at every retract of `f`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-map g) (S : UU l5)
  where

  is-local-retract-map-is-local : is-local g S → is-local f S
  is-local-retract-map-is-local =
    is-equiv-retract-map-is-equiv
      ( precomp f S)
      ( precomp g S)
      ( retract-map-precomp-retract-map f g R S)
```

In fact, the higher coherence of the retract is not needed:

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R₀ : A retract-of X) (R₁ : B retract-of Y)
  (i : coherence-square-maps' (inclusion-retract R₀) f g (inclusion-retract R₁))
  (r :
    coherence-square-maps'
      ( map-retraction-retract R₀)
      ( g)
      ( f)
      ( map-retraction-retract R₁))
  (S : UU l5)
  where

  is-local-retract-map-is-local' : is-local g S → is-local f S
  is-local-retract-map-is-local' =
    is-equiv-retract-map-is-equiv'
      ( precomp f S)
      ( precomp g S)
      ( retract-precomp R₁ S)
      ( retract-precomp R₀ S)
      ( precomp-coherence-square-maps
        ( g)
        ( map-retraction-retract R₀)
        ( map-retraction-retract R₁)
        ( f)
        ( r)
        ( S))
      ( precomp-coherence-square-maps
        ( f)
        ( inclusion-retract R₀)
        ( inclusion-retract R₁)
        ( g)
        ( i)
        ( S))
```

### If every type is `f`-local, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-equiv-is-local : ({l : Level} (A : UU l) → is-local f A) → is-equiv f
  is-equiv-is-local = is-equiv-is-equiv-precomp f
```

### If the domain and codomain of `f` is `f`-local, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  section-is-local-domains' : section (precomp f X) → is-local f Y → section f
  pr1 (section-is-local-domains' section-precomp-X is-local-Y) =
    pr1 section-precomp-X id
  pr2 (section-is-local-domains' section-precomp-X is-local-Y) =
    htpy-eq
      ( ap
        ( pr1)
        { ( f ∘ pr1 (section-is-local-domains' section-precomp-X is-local-Y)) ,
          ( ap (postcomp X f) (pr2 section-precomp-X id))}
        { id , refl}
        ( eq-is-contr (is-contr-map-is-equiv is-local-Y f)))

  is-equiv-is-local-domains' : section (precomp f X) → is-local f Y → is-equiv f
  pr1 (is-equiv-is-local-domains' section-precomp-X is-local-Y) =
    section-is-local-domains' section-precomp-X is-local-Y
  pr2 (is-equiv-is-local-domains' section-precomp-X is-local-Y) =
    retraction-section-precomp-domain f section-precomp-X

  is-equiv-is-local-domains : is-local f X → is-local f Y → is-equiv f
  is-equiv-is-local-domains is-local-X =
    is-equiv-is-local-domains' (pr1 is-local-X)
```

### Propositions are `f`-local if `_∘ f` has a converse

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-local-dependent-type-is-prop :
    {l : Level} (A : Y → UU l) →
    ((y : Y) → is-prop (A y)) →
    (((x : X) → A (f x)) → ((y : Y) → A y)) →
    is-local-dependent-type f A
  is-local-dependent-type-is-prop A is-prop-A =
    is-equiv-has-converse-is-prop
      ( is-prop-Π is-prop-A)
      ( is-prop-Π (is-prop-A ∘ f))

  is-local-is-prop :
    {l : Level} (A : UU l) →
    is-prop A → ((X → A) → (Y → A)) → is-local f A
  is-local-is-prop A is-prop-A =
    is-local-dependent-type-is-prop (λ _ → A) (λ _ → is-prop-A)
```

### All type families are local at equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-local-dependent-type-is-equiv :
    is-equiv f → {l : Level} (A : Y → UU l) → is-local-dependent-type f A
  is-local-dependent-type-is-equiv is-equiv-f =
    is-equiv-precomp-Π-is-equiv is-equiv-f

  is-local-is-equiv :
    is-equiv f → {l : Level} (A : UU l) → is-local f A
  is-local-is-equiv is-equiv-f = is-equiv-precomp-is-equiv f is-equiv-f
```

### Contractible types are local at any map

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-local-dependent-type-is-contr :
    {l : Level} (A : Y → UU l) →
    ((y : Y) → is-contr (A y)) → is-local-dependent-type f A
  is-local-dependent-type-is-contr A is-contr-A =
    is-equiv-is-contr
      ( precomp-Π f A)
      ( is-contr-Π is-contr-A)
      ( is-contr-Π (is-contr-A ∘ f))

  is-local-is-contr :
    {l : Level} (A : UU l) → is-contr A → is-local f A
  is-local-is-contr A is-contr-A =
    is-local-dependent-type-is-contr (λ _ → A) (λ _ → is-contr-A)
```

### A type that is local at the unique map `empty → unit` is contractible

```agda
is-contr-is-local :
  {l : Level} (A : UU l) → is-local (λ (_ : empty) → star) A → is-contr A
is-contr-is-local A is-local-A =
  is-contr-is-equiv
    ( empty → A)
    ( λ a _ → a)
    ( is-equiv-comp
      ( λ a' _ → a' star)
      ( λ a _ →
        map-inv-is-equiv (is-equiv-map-left-unit-law-Π (λ _ → A)) a star)
      ( is-equiv-map-inv-is-equiv (is-equiv-map-left-unit-law-Π (λ _ → A)))
      ( is-local-A))
    ( universal-property-empty' A)
```

## See also

- [Local maps](orthogonal-factorization-systems.maps-local-at-maps.md)
- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-at-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-at-subuniverses.md)
