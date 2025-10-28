# Path-cosplit maps

```agda
module foundation.path-cosplit-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-action-on-identifications-functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.iterated-dependent-product-types
open import foundation.iterated-successors-truncation-levels
open import foundation.logical-equivalences
open import foundation.mere-path-cosplit-maps
open import foundation.morphisms-arrows
open import foundation.negated-equality
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositional-truncations
open import foundation.retractions
open import foundation.retracts-of-maps
open import foundation.truncated-maps
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-types
```

</details>

## Idea

In Homotopy Type Theory, there are multiple nonequivalent ways to state that a
map is "injective" that are more or less informed by the homotopy structures of
its domain and codomain. A
{{#concept "path-cosplit map" Disambiguation="between types" Agda=is-path-cosplit}}
is one such notion, lying somewhere between
[embeddings](foundation-core.embeddings.md) and
[injective maps](foundation-core.injective-maps.md). In fact, given an integer
`k ≥ -2`, if we understand `k`-injective map to mean the `k+2`-dimensional
[action on identifications](foundation.action-on-higher-identifications-functions.md)
has a converse map, then we have proper inclusions

```text
  k-injective maps ⊃ k-path-cosplit maps ⊃ k-truncated maps.
```

While `k`-truncatedness answers the question:

> At which dimension is the action on higher identifications of a function
> always an [equivalence](foundation-core.equivalences.md)?

Being `k`-path-cosplitting instead answers the question:

> At which dimension is the action a
> [retract](foundation-core.retracts-of-types.md)?

Thus a _`-2`-path-cosplit map_ is a map equipped with a
[retraction](foundation-core.retractions.md). A _`k+1`-path-cosplit map_ is a
map whose
[action on identifications](foundation.action-on-identifications-functions.md)
is `k`-path-cosplit.

We show that `k`-path-cosplittness coincides with `k`-truncatedness when the
codomain is `k`-truncated, but more generally `k`-path-cosplitting may only
induce retracts on higher homotopy groups.

## Definitions

### The predicate on a map of being path-cosplit

```agda
is-path-cosplit :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-path-cosplit neg-two-𝕋 f = retraction f
is-path-cosplit (succ-𝕋 k) {A} f = (x y : A) → is-path-cosplit k (ap f {x} {y})
```

### The type of path-cosplit maps between two types

```agda
path-cosplit-map :
  {l1 l2 : Level} → 𝕋 → UU l1 → UU l2 → UU (l1 ⊔ l2)
path-cosplit-map k A B = Σ (A → B) (is-path-cosplit k)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : path-cosplit-map k A B)
  where

  map-path-cosplit-map : A → B
  map-path-cosplit-map = pr1 f

  is-path-cosplit-path-cosplit-map : is-path-cosplit k map-path-cosplit-map
  is-path-cosplit-path-cosplit-map = pr2 f
```

### The type of path-cosplittings of a type

```agda
path-cosplitting :
  (l1 : Level) {l2 : Level} → 𝕋 → UU l2 → UU (lsuc l1 ⊔ l2)
path-cosplitting l1 k B = Σ (UU l1) (λ A → path-cosplit-map k A B)

module _
  {l1 l2 : Level} {k : 𝕋} {B : UU l2} (H : path-cosplitting l1 k B)
  where

  type-path-cosplitting : UU l1
  type-path-cosplitting = pr1 H

  path-cosplit-map-path-cosplitting : path-cosplit-map k type-path-cosplitting B
  path-cosplit-map-path-cosplitting = pr2 H

  map-path-cosplitting : type-path-cosplitting → B
  map-path-cosplitting = map-path-cosplit-map path-cosplit-map-path-cosplitting

  is-path-cosplit-map-path-cosplitting : is-path-cosplit k map-path-cosplitting
  is-path-cosplit-map-path-cosplitting =
    is-path-cosplit-path-cosplit-map path-cosplit-map-path-cosplitting
```

## Properties

### If a map is `k`-path-cosplit it is merely `k`-path-cosplit

```agda
is-mere-path-cosplit-is-path-cosplit :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-path-cosplit k f → is-mere-path-cosplit k f
is-mere-path-cosplit-is-path-cosplit neg-two-𝕋 is-cosplit-f =
  unit-trunc-Prop is-cosplit-f
is-mere-path-cosplit-is-path-cosplit (succ-𝕋 k) is-cosplit-f x y =
  is-mere-path-cosplit-is-path-cosplit k (is-cosplit-f x y)
```

### If a map is `k`-truncated then it is `k`-path-cosplit

```agda
is-path-cosplit-is-trunc :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-trunc-map k f → is-path-cosplit k f
is-path-cosplit-is-trunc neg-two-𝕋 is-trunc-f =
  retraction-is-contr-map is-trunc-f
is-path-cosplit-is-trunc (succ-𝕋 k) {f = f} is-trunc-f x y =
  is-path-cosplit-is-trunc k (is-trunc-map-ap-is-trunc-map k f is-trunc-f x y)
```

### If a map is `k`-path-cosplit then it is `k+1`-path-cosplit

```agda
is-path-cosplit-succ-is-path-cosplit :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-path-cosplit k f → is-path-cosplit (succ-𝕋 k) f
is-path-cosplit-succ-is-path-cosplit neg-two-𝕋 {f = f} is-cosplit-f x y =
  retraction-ap f is-cosplit-f
is-path-cosplit-succ-is-path-cosplit (succ-𝕋 k) is-cosplit-f x y =
  is-path-cosplit-succ-is-path-cosplit k (is-cosplit-f x y)
```

### If a map is `k`-path-cosplit then it is `k+r`-path-cosplit for every `r ≥ 0`

```agda
is-path-cosplit-iterated-succ-is-path-cosplit :
  {l1 l2 : Level} (k : 𝕋) (r : ℕ) {A : UU l1} {B : UU l2} {f : A → B} →
  is-path-cosplit k f → is-path-cosplit (iterate-succ-𝕋 r k) f
is-path-cosplit-iterated-succ-is-path-cosplit k zero-ℕ = id
is-path-cosplit-iterated-succ-is-path-cosplit k (succ-ℕ r) F =
  is-path-cosplit-iterated-succ-is-path-cosplit (succ-𝕋 k) r
    ( is-path-cosplit-succ-is-path-cosplit k F)
```

### Retracts are `k`-path-cosplit for every `k`

```agda
is-path-cosplit-retraction :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  retraction f → is-path-cosplit k f
is-path-cosplit-retraction neg-two-𝕋 H = H
is-path-cosplit-retraction (succ-𝕋 k) H =
  is-path-cosplit-succ-is-path-cosplit k (is-path-cosplit-retraction k H)
```

### Equivalences are `k`-path-cosplit for every `k`

```agda
is-path-cosplit-is-equiv :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-path-cosplit k f
is-path-cosplit-is-equiv k H =
  is-path-cosplit-retraction k (retraction-is-equiv H)
```

### The identity map is `k`-path-cosplit for every `k`

```agda
is-path-cosplit-id :
  {l : Level} (k : 𝕋) {A : UU l} → is-path-cosplit k (id {A = A})
is-path-cosplit-id k = is-path-cosplit-retraction k (id , refl-htpy)
```

### If a type maps into a `k`-truncated type via a `k`-path-cosplit map then it is `k`-truncated

```agda
is-trunc-domain-is-path-cosplit-is-trunc-codomain :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-trunc k B → is-path-cosplit k f → is-trunc k A
is-trunc-domain-is-path-cosplit-is-trunc-codomain neg-two-𝕋
  {A} {B} {f} is-trunc-B is-cosplit-f =
  is-trunc-retract-of (f , is-cosplit-f) is-trunc-B
is-trunc-domain-is-path-cosplit-is-trunc-codomain
  (succ-𝕋 k) {A} {B} {f} is-trunc-B is-cosplit-f x y =
  is-trunc-domain-is-path-cosplit-is-trunc-codomain k
    ( is-trunc-B (f x) (f y))
    ( is-cosplit-f x y)
```

This result generalizes the following statements:

- A type that injects into a set is a set.

- A type that embeds into a `k+1`-truncated type is `k+1`-truncated.

- A type that maps into a `k`-truncated type via a `k`-truncated map is
  `k`-truncated.

### If the codomain of a `k`-path-cosplit map is `k`-truncated then the map is `k`-truncated

```agda
is-trunc-map-is-path-cosplit-is-trunc-codomain :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-trunc k B → is-path-cosplit k f → is-trunc-map k f
is-trunc-map-is-path-cosplit-is-trunc-codomain k is-trunc-B is-cosplit-f =
  is-trunc-map-is-trunc-domain-codomain k
    ( is-trunc-domain-is-path-cosplit-is-trunc-codomain k
      ( is-trunc-B)
      ( is-cosplit-f))
    ( is-trunc-B)
```

### If the domain is `k+r+2`-truncated, the type of `k`-path-cosplittings of `f` is `r`-truncated

```agda
is-trunc-is-path-cosplit-is-trunc-succ-domain :
  {l1 l2 : Level} {k r : 𝕋} {A : UU l1} {B : UU l2} {f : A → B} →
  is-trunc (add+2-𝕋 r k) A → is-trunc r (is-path-cosplit k f)
is-trunc-is-path-cosplit-is-trunc-succ-domain {k = neg-two-𝕋} =
  is-trunc-retraction
is-trunc-is-path-cosplit-is-trunc-succ-domain {k = succ-𝕋 k} {r} is-trunc-A =
  is-trunc-Π r
    ( λ x →
      is-trunc-Π r
        ( λ y → is-trunc-is-path-cosplit-is-trunc-succ-domain (is-trunc-A x y)))
```

### If the domain is `k+1`-truncated then `k`-path-cosplittings of `f` are unique

```agda
is-prop-is-path-cosplit-is-trunc-succ-domain :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B} →
  is-trunc (succ-𝕋 k) A → is-prop (is-path-cosplit k f)
is-prop-is-path-cosplit-is-trunc-succ-domain {k = neg-two-𝕋} =
  is-prop-retraction
is-prop-is-path-cosplit-is-trunc-succ-domain {k = succ-𝕋 k} is-trunc-A =
  is-prop-Π
    ( λ x →
      is-prop-Π
        ( λ y → is-prop-is-path-cosplit-is-trunc-succ-domain (is-trunc-A x y)))
```

### If the domain is `k`-truncated then there is a unique `k`-path-cosplitting of `f`

```agda
is-contr-is-path-cosplit-is-trunc-domain :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B} →
  is-trunc k A → is-contr (is-path-cosplit k f)
is-contr-is-path-cosplit-is-trunc-domain {k = neg-two-𝕋} =
  is-contr-retraction
is-contr-is-path-cosplit-is-trunc-domain {k = succ-𝕋 k} is-trunc-A =
  is-contr-Π
    ( λ x →
      is-contr-Π
        ( λ y → is-contr-is-path-cosplit-is-trunc-domain (is-trunc-A x y)))
```

### Path-cosplit maps are closed under morphisms of maps that are path-cosplit on the domain

Given a commuting diagram of the form

```text
         i
    A ------> X
    |         |
  f |         | g
    ∨         ∨
    B ------> Y.
         j
```

then if `g` and `i` are `k`-path cosplit, so is `f`.

```agda
is-path-cosplit-is-path-cosplit-on-domain-hom-arrow :
  {l1 l2 l3 l4 : Level} {k : 𝕋}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g) →
  is-path-cosplit k (map-domain-hom-arrow f g α) →
  is-path-cosplit k g →
  is-path-cosplit k f
is-path-cosplit-is-path-cosplit-on-domain-hom-arrow
  {k = neg-two-𝕋} f g α I =
  retraction-retract-map-retraction' f g
    ( map-domain-hom-arrow f g α , I)
    ( map-codomain-hom-arrow f g α)
    ( coh-hom-arrow f g α)
is-path-cosplit-is-path-cosplit-on-domain-hom-arrow
  {k = succ-𝕋 k} f g α I G x y =
  is-path-cosplit-is-path-cosplit-on-domain-hom-arrow
    ( ap f)
    ( ap g)
    ( ap-hom-arrow f g α)
    ( I x y)
    ( G (map-domain-hom-arrow f g α x) (map-domain-hom-arrow f g α y))
```

### In a commuting triangle, if the left map is path-cosplit then so is the top map

Given a triangle of the form

```text
        top
    A ------> B
      \     /
  left \   / right
        ∨ ∨
         C,
```

if the left map is `k`-path-cosplit then so is the top map.

```agda
is-path-cosplit-top-map-triangle' :
  {l1 l2 l3 : Level} {k : 𝕋}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (top : A → B) (left : A → C) (right : B → C)
  (H : coherence-triangle-maps' left right top) →
  is-path-cosplit k left → is-path-cosplit k top
is-path-cosplit-top-map-triangle' top left right H =
  is-path-cosplit-is-path-cosplit-on-domain-hom-arrow top left
    ( id , right , H)
    ( is-path-cosplit-id _)
```

### In a commuting triangle if the top and right map are path-cosplit then so is the left map

Given a triangle of the form

```text
        top
    A ------> B
      \     /
  left \   / right
        ∨ ∨
         C,
```

if the top and right map are `k`-path-cosplit then so is the left map.

```agda
is-path-cosplit-left-map-triangle :
  {l1 l2 l3 : Level} {k : 𝕋}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (top : A → B) (left : A → C) (right : B → C)
  (H : coherence-triangle-maps left right top) →
  is-path-cosplit k top → is-path-cosplit k right → is-path-cosplit k left
is-path-cosplit-left-map-triangle top left right H =
  is-path-cosplit-is-path-cosplit-on-domain-hom-arrow left right
    ( top , id , H)
```

### Path-cosplit maps are closed under equivalences of maps

```agda
is-path-cosplit-equiv-arrow :
  {l1 l2 l3 l4 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (α : equiv-arrow f g) →
  is-path-cosplit k g → is-path-cosplit k f
is-path-cosplit-equiv-arrow {f = f} {g} α =
  is-path-cosplit-is-path-cosplit-on-domain-hom-arrow f g
    ( hom-equiv-arrow f g α)
    ( is-path-cosplit-is-equiv _ (is-equiv-map-domain-equiv-arrow f g α))

is-path-cosplit-equiv-arrow' :
  {l1 l2 l3 l4 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (α : equiv-arrow f g) →
  is-path-cosplit k f → is-path-cosplit k g
is-path-cosplit-equiv-arrow' {f = f} {g} α =
  is-path-cosplit-equiv-arrow (inv-equiv-arrow f g α)
```

### Path-cosplit maps are closed under homotopy

```agda
is-path-cosplit-htpy :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f g : A → B} →
  f ~ g → is-path-cosplit k g → is-path-cosplit k f
is-path-cosplit-htpy H =
  is-path-cosplit-is-path-cosplit-on-domain-hom-arrow _ _
    ( id , id , H)
    ( is-path-cosplit-id _)
```

### Path-cosplit maps compose

```agda
is-path-cosplit-comp :
  {l1 l2 l3 : Level} {k : 𝕋}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B} →
  is-path-cosplit k g → is-path-cosplit k f → is-path-cosplit k (g ∘ f)
is-path-cosplit-comp G F = is-path-cosplit-left-map-triangle _ _ _ refl-htpy F G
```

### Families of path-cosplit maps induce path-cosplittings on dependent products

```agda
abstract
  is-path-cosplit-map-Π-is-fiberwise-path-cosplit :
    {l1 l2 l3 : Level} {k : 𝕋} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    {f : (i : I) → A i → B i} →
    ((i : I) → is-path-cosplit k (f i)) → is-path-cosplit k (map-Π f)
  is-path-cosplit-map-Π-is-fiberwise-path-cosplit {k = neg-two-𝕋} =
    retraction-map-Π-fiberwise-retraction
  is-path-cosplit-map-Π-is-fiberwise-path-cosplit {k = succ-𝕋 k} {f = f} F x y =
    is-path-cosplit-equiv-arrow
      ( equiv-funext , equiv-funext , (λ where refl → refl))
      ( is-path-cosplit-map-Π-is-fiberwise-path-cosplit (λ i → F i (x i) (y i)))
```

### If a map is path-cosplit then postcomposing by it is path-cosplit

```agda
is-path-cosplit-postcomp :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B} →
  is-path-cosplit k f → (S : UU l3) → is-path-cosplit k (postcomp S f)
is-path-cosplit-postcomp F S =
  is-path-cosplit-map-Π-is-fiberwise-path-cosplit (λ _ → F)
```

### Products of path-cosplit maps are path-cosplit

```agda
is-path-cosplit-map-product :
  {l1 l2 l3 l4 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} →
  is-path-cosplit k f →
  is-path-cosplit k g →
  is-path-cosplit k (map-product f g)
is-path-cosplit-map-product {k = neg-two-𝕋} {f = f} {g} =
  retraction-map-product f g
is-path-cosplit-map-product {k = succ-𝕋 k} {f = f} {g} F G x y =
  is-path-cosplit-equiv-arrow
    ( ( equiv-pair-eq x y) ,
      ( equiv-pair-eq (map-product f g x) (map-product f g y)) ,
      ( compute-ap-map-product f g))
    ( is-path-cosplit-map-product (F (pr1 x) (pr1 y)) (G (pr2 x) (pr2 y)))
```

### The total map of a family of path-cosplit maps is path-cosplit

```agda
is-path-cosplit-tot :
  {l1 l2 l3 : Level} {k : 𝕋}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3} {f : (i : I) → A i → B i} →
  ((i : I) → is-path-cosplit k (f i)) →
  is-path-cosplit k (tot f)
is-path-cosplit-tot {k = neg-two-𝕋} =
  retraction-tot
is-path-cosplit-tot {k = succ-𝕋 k} {f = f} F x y =
  is-path-cosplit-equiv-arrow
    ( equiv-pair-eq-Σ x y ,
      equiv-pair-eq-Σ (tot f x) (tot f y) ,
      coh-ap-tot f)
    ( is-path-cosplit-tot
      { f = λ p q → inv (preserves-tr f p (pr2 x)) ∙ ap (f (pr1 y)) q}
      ( λ where refl → F (pr1 y) (pr2 x) (pr2 y)))
```

### A map `A + B → C` defined by maps `f : A → C` and `B → C` is path-cosplit if both `f` and `g` are path-cosplit and they don't overlap

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋}
  {A : UU l1} {B : UU l2} {C : UU l3} {f : A → C} {g : B → C}
  where

  abstract
    is-path-cosplit-succ-coproduct :
      is-path-cosplit (succ-𝕋 k) f →
      is-path-cosplit (succ-𝕋 k) g →
      ((a : A) (b : B) → f a ≠ g b) →
      is-path-cosplit (succ-𝕋 k) (rec-coproduct f g)
    is-path-cosplit-succ-coproduct F G N (inl x) (inl y) =
      is-path-cosplit-equiv-arrow'
        ( equiv-ap-emb emb-inl , id-equiv , λ where refl → refl)
        ( F x y)
    is-path-cosplit-succ-coproduct F G N (inl x) (inr y) =
      is-path-cosplit-is-equiv k
        ( is-equiv-is-empty (ap (rec-coproduct f g)) (N x y))
    is-path-cosplit-succ-coproduct F G N (inr x) (inl y) =
      is-path-cosplit-is-equiv k
        ( is-equiv-is-empty (ap (rec-coproduct f g)) (N y x ∘ inv))
    is-path-cosplit-succ-coproduct F G N (inr x) (inr y) =
      is-path-cosplit-equiv-arrow'
        ( equiv-ap-emb emb-inr , id-equiv , λ where refl → refl)
        ( G x y)
```

### Coproducts of path-cosplit maps are path-cosplit

```agda
abstract
  is-path-cosplit-succ-map-coproduct :
    {l1 l2 l3 l4 : Level} {k : 𝕋}
    {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    {f : A → B} {g : X → Y} →
    is-path-cosplit (succ-𝕋 k) f →
    is-path-cosplit (succ-𝕋 k) g →
    is-path-cosplit (succ-𝕋 k) (map-coproduct f g)
  is-path-cosplit-succ-map-coproduct {f = f} {g} F G (inl x) (inl y) =
    is-path-cosplit-equiv-arrow
      ( compute-eq-coproduct-inl-inl x y ,
        compute-eq-coproduct-inl-inl (f x) (f y) ,
        λ where refl → refl)
      ( F x y)
  is-path-cosplit-succ-map-coproduct {k = k} {f = f} {g} F G (inl x) (inr y) =
    is-path-cosplit-is-equiv k
      ( is-equiv-is-empty
        ( ap (map-coproduct f g))
        ( is-empty-eq-coproduct-inl-inr (f x) (g y)))
  is-path-cosplit-succ-map-coproduct {k = k} {f = f} {g} F G (inr x) (inl y) =
    is-path-cosplit-is-equiv k
      ( is-equiv-is-empty
        ( ap (map-coproduct f g))
        ( is-empty-eq-coproduct-inr-inl (g x) (f y)))
  is-path-cosplit-succ-map-coproduct {f = f} {g} F G (inr x) (inr y) =
    is-path-cosplit-equiv-arrow
      ( compute-eq-coproduct-inr-inr x y ,
        compute-eq-coproduct-inr-inr (g x) (g y) ,
        λ where refl → refl)
      ( G x y)

is-path-cosplit-map-coproduct :
  {l1 l2 l3 l4 : Level} {k : 𝕋}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} →
  is-path-cosplit k f →
  is-path-cosplit k g →
  is-path-cosplit k (map-coproduct f g)
is-path-cosplit-map-coproduct {k = neg-two-𝕋} =
  retraction-map-coproduct
is-path-cosplit-map-coproduct {k = succ-𝕋 k} =
  is-path-cosplit-succ-map-coproduct
```

## See also

- In [Split-idempotent maps](foundation.split-idempotent-maps.md) we show that
  locally small types are closed under `-1`-path-cosplit maps.
- [Mere path-cosplit maps](foundation.mere-path-cosplit-maps.md)
