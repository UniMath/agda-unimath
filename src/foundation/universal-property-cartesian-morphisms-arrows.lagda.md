# The universal property of cartesian morphisms of arrows

```agda
module foundation.universal-property-cartesian-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.commuting-triangles-of-maps
open import foundation.commuting-triangles-of-morphisms-arrows
open import foundation.cones-over-cospan-diagrams
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproducts-pullbacks
open import foundation.dependent-pair-types
open import foundation.dependent-products-pullbacks
open import foundation.dependent-sums-pullbacks
open import foundation.diagonal-maps-cartesian-products-of-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.homotopies-morphisms-arrows
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.lifts-morphisms-arrows
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.postcomposition-pullbacks
open import foundation.products-pullbacks
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.propositions
open import foundation-core.universal-property-pullbacks

open import orthogonal-factorization-systems.lifts-maps
```

</details>

## Idea

A [morphism of arrows](foundation.morphisms-arrows.md) `β : g ⇒ h`, is said to
satisfy the
{{#concept "universal property" Disambiguation="cartesian morphisms of arrows" Agda=universal-property-cartesian-hom-arrow}}
of [cartesian morphisms](foundation.cartesian-morphisms-arrows.md) of arrows if,
for every morphism of arrows `α : f ⇒ h`, each
[lift](orthogonal-factorization-systems.lifts-maps.md) on the codomain `α₁`
along `β₁` extends uniquely to a
[lifting diagram](foundation.lifts-morphisms-arrows.md) of the morphism of
arrows along `β`.

The way we formalize this is to state that the natural map that assigns to every
lifting diagram of `α` along `β` the underlying lift on the codomain, is an
equivalence. In other words, the natural map takes a lifting diagram of the form

```text
          B
        ∧ | \
       /  |  \
      /   g   ∨
    A --------> C
    |     |     |
    |     ∨     |
  f |     B'    | h
    |   ∧   \   |
    |  /     \  |
    ∨ /       ∨ ∨
    A' -------> C',
```

and returns the underlying diagram

```text
          B'
        ∧   \
     i /     \ β₁
      /       ∨
    A' -------> C'.
          α₁
```

## Definitions

### The universal property of cartesian morphisms of arrows

```agda
module _
  {l3 l4 l5 l6 : Level}
  {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (g : B → B') (h : C → C') (β : hom-arrow g h)
  where

  universal-property-cartesian-hom-arrow-Level :
    (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  universal-property-cartesian-hom-arrow-Level l1 l2 =
    {A : UU l1} {A' : UU l2} (f : A → A') (α : hom-arrow f h) →
    is-equiv (lift-codomain-lift-hom-arrow f g h β α)

  universal-property-cartesian-hom-arrow : UUω
  universal-property-cartesian-hom-arrow =
    {l1 l2 : Level} → universal-property-cartesian-hom-arrow-Level l1 l2
```

### The property of having unique lifts of lifts of the codomain

```agda
module _
  {l3 l4 l5 l6 : Level}
  {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (g : B → B') (h : C → C') (β : hom-arrow g h)
  where

  has-unique-lifts-hom-arrow-Level :
    (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  has-unique-lifts-hom-arrow-Level l1 l2 =
    {A : UU l1} {A' : UU l2} (f : A → A') (α : hom-arrow f h) →
    (δ :
      lift-map (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α)) →
    is-contr (lift-hom-arrow-of-lift-codomain-hom-arrow f g h β α δ)

  has-unique-lifts-hom-arrow : UUω
  has-unique-lifts-hom-arrow =
    {l1 l2 : Level} → has-unique-lifts-hom-arrow-Level l1 l2
```

## Properties

### A morphism of arrows satisfies the universal property of cartesian morphisms if and only if it has unique lifts

```agda
module _
  {l3 l4 l5 l6 : Level}
  {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (g : B → B') (h : C → C') (β : hom-arrow g h)
  where

  abstract
    has-unique-lifts-up-cartesian-hom-arrow :
      universal-property-cartesian-hom-arrow g h β →
      has-unique-lifts-hom-arrow g h β
    has-unique-lifts-up-cartesian-hom-arrow up-β f α δ =
      is-contr-equiv' _
        ( compute-fiber-lift-codomain-lift-hom-arrow f g h β α δ)
        ( is-contr-map-is-equiv (up-β f α) δ)

  abstract
    up-cartesian-has-unique-lifts-hom-arrow :
      has-unique-lifts-hom-arrow g h β →
      universal-property-cartesian-hom-arrow g h β
    up-cartesian-has-unique-lifts-hom-arrow L f α =
      is-equiv-is-contr-map
        ( λ δ →
          is-contr-equiv _
            ( compute-fiber-lift-codomain-lift-hom-arrow f g h β α δ)
            ( L f α δ))
```

### A morphism of arrows has unique lifts if and only if it is cartesian

```agda
module _
  {l3 l4 l5 l6 : Level}
  {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (g : B → B') (h : C → C') (β : hom-arrow g h)
  where

  abstract
    has-unique-lifts-is-cartesian-hom-arrow :
      is-cartesian-hom-arrow g h β →
      has-unique-lifts-hom-arrow g h β
    has-unique-lifts-is-cartesian-hom-arrow H {A = A} f α (i , I) =
      is-contr-equiv _
        ( equiv-tot
          ( equiv-htpy-cone-is-lift-hom-arrow-of-lift-codomain-hom-arrow
            f g h β α (i , I)))
        ( uniqueness-universal-property-pullback
          ( map-codomain-hom-arrow g h β)
          ( h)
          ( cone-hom-arrow g h β)
          ( up-pullback-cartesian-hom-arrow g h (β , H))
          ( A)
          ( i ∘ f ,
            map-domain-hom-arrow f h α ,
            inv-htpy I ·r f ∙h coh-hom-arrow f h α))

  abstract
    is-cartesian-has-unique-lifts-hom-arrow :
      has-unique-lifts-hom-arrow g h β →
      is-cartesian-hom-arrow g h β
    is-cartesian-has-unique-lifts-hom-arrow H =
      is-pullback-universal-property-pullback
        ( map-codomain-hom-arrow g h β)
        ( h)
        ( cone-hom-arrow g h β)
        ( universal-property-pullback-uniqueness
          ( map-codomain-hom-arrow g h β)
          ( h)
          ( cone-hom-arrow g h β)
          ( λ A (f , i , I) →
            ( is-contr-equiv' _
              ( equiv-tot
                ( equiv-htpy-cone-is-lift-hom-arrow-of-lift-codomain-hom-arrow
                  ( f)
                  ( g)
                  ( h)
                  ( β)
                  ( i , map-codomain-hom-arrow g h β , I)
                  ( id , refl-htpy)))
              ( H f (i , map-codomain-hom-arrow g h β , I) (id , refl-htpy)))))
```

### A morphism of arrows satisfies the universal property of cartesian morphisms if and only if it is cartesian

```agda
module _
  {l3 l4 l5 l6 : Level}
  {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (g : B → B') (h : C → C') (β : hom-arrow g h)
  where

  abstract
    up-cartesian-is-cartesian-hom-arrow :
      is-cartesian-hom-arrow g h β →
      universal-property-cartesian-hom-arrow g h β
    up-cartesian-is-cartesian-hom-arrow H =
      up-cartesian-has-unique-lifts-hom-arrow g h β
        ( has-unique-lifts-is-cartesian-hom-arrow g h β H)

  abstract
    is-cartesian-up-cartesian-hom-arrow :
      universal-property-cartesian-hom-arrow g h β →
      is-cartesian-hom-arrow g h β
    is-cartesian-up-cartesian-hom-arrow H =
      is-cartesian-has-unique-lifts-hom-arrow g h β
        ( has-unique-lifts-up-cartesian-hom-arrow g h β H)
```

### Explicit construction of lifts along cartesian morphisms

> The following computation is obsoleted by the formalizations above, but are
> preserved for potential instructive value.

Suppose given a cospan diagram of arrows

```text
    A ------> C <------ B
    |         |       ⌞ |
  f |    α    h    β    | g
    ∨         ∨         ∨
    A' -----> C' <----- B'
```

where `β` is cartesian. Moreover, suppose we have a map `i : A' → B'` from the
codomain of the source of `α` to the codomain of the source of `β` such that the
triangle

```text
         i
     A' ---> B'
      \     /
       \   /
        ∨ ∨
         C'
```

commutes. Then there is a unique morphism of arrows `γ : f → g` with a homotopy
`β ~ α ∘ γ` extending the triangle, and this morphism is cartesian if and only
if `α` is.

**Proof.** The unique existence of `γ` and the homotopy follows from the
pullback property of `β`. The rest is a reiteration of the 3-for-2 property of
cartesian morphisms. ∎

We construct the commuting triangle of morphisms of arrows:

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (β : cartesian-hom-arrow g h)
  (α : hom-arrow f h)
  (i : A' → B')
  (H :
    coherence-triangle-maps'
      ( map-codomain-hom-arrow f h α)
      ( map-codomain-cartesian-hom-arrow g h β)
      ( i))
  where

  cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
    cone (map-codomain-cartesian-hom-arrow g h β) h A
  cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    ( i ∘ f , map-domain-hom-arrow f h α , H ·r f ∙h coh-hom-arrow f h α)

  map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow : A → B
  map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    gap-is-pullback
      ( map-codomain-cartesian-hom-arrow g h β)
      ( h)
      ( cone-cartesian-hom-arrow g h β)
      ( is-cartesian-cartesian-hom-arrow g h β)
      ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)

  hom-arrow-lift-map-codomain-cartesian-hom-arrow : hom-arrow f g
  pr1 hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow
  pr1 (pr2 hom-arrow-lift-map-codomain-cartesian-hom-arrow) = i
  pr2 (pr2 hom-arrow-lift-map-codomain-cartesian-hom-arrow) =
    inv-htpy
      ( htpy-vertical-map-gap-is-pullback
        ( map-codomain-cartesian-hom-arrow g h β)
        ( h)
        ( cone-cartesian-hom-arrow g h β)
        ( is-cartesian-cartesian-hom-arrow g h β)
        ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow))

  abstract
    inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
      coherence-triangle-hom-arrow' f g h
        ( α)
        ( hom-arrow-cartesian-hom-arrow g h β)
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrow)
    inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
      ( htpy-horizontal-map-gap-is-pullback
          ( map-codomain-cartesian-hom-arrow g h β)
          ( h)
          ( cone-cartesian-hom-arrow g h β)
          ( is-cartesian-cartesian-hom-arrow g h β)
          ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)) ,
      ( H) ,
      ( ( ap-concat-htpy'
          ( ( h) ·l
            ( htpy-horizontal-map-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( pr2 β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))
          ( ap-concat-htpy'
            ( coh-cartesian-hom-arrow g h β ·r
              map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow)
            ( left-whisker-inv-htpy
              ( map-codomain-cartesian-hom-arrow g h β)
              ( htpy-vertical-map-gap-is-pullback
                ( map-codomain-cartesian-hom-arrow g h β)
                ( h)
                ( cone-cartesian-hom-arrow g h β)
                ( pr2 β)
                ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow))))) ∙h
        ( assoc-htpy
          ( inv-htpy
            ( ( map-codomain-cartesian-hom-arrow g h β) ·l
              ( htpy-vertical-map-gap-is-pullback
                ( map-codomain-cartesian-hom-arrow g h β)
                ( h)
                ( cone-cartesian-hom-arrow g h β)
                ( pr2 β)
                ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow))))
          ( coh-cartesian-hom-arrow g h β ·r
            map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow)
          ( ( h) ·l
            ( htpy-horizontal-map-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( pr2 β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))) ∙h
        ( inv-htpy-left-transpose-htpy-concat
          ( ( map-codomain-cartesian-hom-arrow g h β) ·l
            ( htpy-vertical-map-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( pr2 β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))
          ( H ·r f ∙h coh-hom-arrow f h α)
          ( ( coh-cartesian-hom-arrow g h β ·r
              map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow) ∙h
            ( h) ·l
            ( htpy-horizontal-map-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( is-cartesian-cartesian-hom-arrow g h β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))
          ( inv-htpy
            ( coh-htpy-cone-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( is-cartesian-cartesian-hom-arrow g h β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))))

  coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
    coherence-triangle-hom-arrow f g h
      ( α)
      ( hom-arrow-cartesian-hom-arrow g h β)
      ( hom-arrow-lift-map-codomain-cartesian-hom-arrow)
  coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    inv-htpy-hom-arrow f h
      ( comp-hom-arrow f g h
        ( hom-arrow-cartesian-hom-arrow g h β)
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrow))
      ( α)
      ( inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow)
```

If `α` was cartesian to begin with, the lift is also.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (β : cartesian-hom-arrow g h)
  (α : cartesian-hom-arrow f h)
  (i : A' → B')
  (H :
    coherence-triangle-maps'
      ( map-codomain-cartesian-hom-arrow f h α)
      ( map-codomain-cartesian-hom-arrow g h β)
      ( i))
  where

  abstract
    is-cartesian-cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
      is-cartesian-hom-arrow f g
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrow f g h
          ( β)
          ( hom-arrow-cartesian-hom-arrow f h α)
          ( i)
          ( H))
    is-cartesian-cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
      is-cartesian-top-cartesian-hom-arrow-triangle' f g h
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrow f g h
          ( β)
          ( hom-arrow-cartesian-hom-arrow f h α)
          ( i)
          ( H))
        ( α)
        ( β)
        ( inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow
          ( f) g h β (hom-arrow-cartesian-hom-arrow f h α) i H)

  cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
    cartesian-hom-arrow f g
  cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    ( hom-arrow-lift-map-codomain-cartesian-hom-arrow
      ( f) g h β (hom-arrow-cartesian-hom-arrow f h α) i H) ,
    ( is-cartesian-cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow)
```
