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
open import foundation.contractible-types
open import foundation.coproducts-pullbacks
open import foundation.dependent-pair-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.dependent-products-pullbacks
open import foundation.dependent-sums-pullbacks
open import foundation.diagonal-maps-cartesian-products-of-types
open import foundation.equivalences
open import foundation.homotopy-induction
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.homotopies-morphisms-arrows
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

A [morphism of arrows](foundation.morphisms-arrows.md) `β : g ⇒ h`,

```text
         β₀
    B ------> C
    |         |
  g |    H    | h
    ∨         ∨
    B' -----> C',
         β₁
```

is said to satisfy the
{{#concept "universal property" Disambiguation="cartesian morphisms of arrows"}}
of cartesian morphisms of arrows if the natural map that assigns to every
extension diagram of the form

```text
          B
        ∧ | \
       /  |  \
      /   g   ∨
    A --------> C
    |     |     |
    |     ∨  H  |
  f |     B'    | h
    |   ∧   \β₁ |
    |  /     \  |
    ∨ /       ∨ ∨
    A' -------> C'
```

the underlying data

```text
    A --------> C
    |           |
    |        H  |
  f |     B'    | h
    |   ∧   \β₁ |
    | i/     \  |
    ∨ /       ∨ ∨
    A' -------> C'
```

is an equivalence.

## Definitions

```agda
lift-codomain-lift-hom-arrow :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (α : hom-arrow f h) (β : hom-arrow g h) →
  lift-hom-arrow f g h α β →
  lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α)
lift-codomain-lift-hom-arrow f g h α β γ =
  ( map-codomain-lift-hom-arrow f g h α β γ ,
    coh-codomain-lift-hom-arrow f g h α β γ)
```

### The universal property of cartesian morphisms of arrows

```agda
universal-property-cartesian-hom-arrow-Level :
  (l1 l2 : Level) {l3 l4 l5 l6 : Level}
  {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (g : B → B') (h : C → C') (β : hom-arrow g h) →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
universal-property-cartesian-hom-arrow-Level l1 l2 g h β =
  {A : UU l1} {A' : UU l2} (f : A → A') (α : hom-arrow f h) →
  is-equiv (lift-codomain-lift-hom-arrow f g h α β)

universal-property-cartesian-hom-arrow :
  {l3 l4 l5 l6 : Level}
  {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (g : B → B') (h : C → C') (β : hom-arrow g h) →
  UUω
universal-property-cartesian-hom-arrow g h β =
  {l1 l2 : Level} → universal-property-cartesian-hom-arrow-Level l1 l2 g h β
```

## Properties

### Computing the fibers of `lift-codomain-lift-hom-arrow`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (α : hom-arrow f h) (β : hom-arrow g h)
  ( let β₁ = map-codomain-hom-arrow g h β)
  where

  is-lift-hom-arrow-of-lift-codomain-hom-arrow :
    lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α) →
    (A → B) → UU (l1 ⊔ l4 ⊔ l5 ⊔ l6)
  is-lift-hom-arrow-of-lift-codomain-hom-arrow (i , I) j =
    Σ ( coherence-hom-arrow f g j i)
      ( λ H →
        Σ ( coherence-triangle-maps
            ( map-domain-hom-arrow f h α)
            ( map-domain-hom-arrow g h β)
            ( j))
          ( λ J →
            coherence-htpy-hom-arrow f h α
              ( comp-hom-arrow f g h β (j , i , H))
              ( J)
              ( I)))

  lift-hom-arrow-of-lift-codomain-hom-arrow :
    lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α) →
    UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  lift-hom-arrow-of-lift-codomain-hom-arrow i =
    Σ (A → B) (is-lift-hom-arrow-of-lift-codomain-hom-arrow i)

  compute-fiber-lift-codomain-lift-hom-arrow :
    (δ : lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α)) →
    fiber (lift-codomain-lift-hom-arrow f g h α β) δ ≃
    lift-hom-arrow-of-lift-codomain-hom-arrow δ
  compute-fiber-lift-codomain-lift-hom-arrow (δ , Hδ) =
    equivalence-reasoning
    Σ ( lift-hom-arrow f g h α β)
      ( λ γ → lift-codomain-lift-hom-arrow f g h α β γ ＝ (δ , Hδ))
    ≃ Σ ( lift-hom-arrow f g h α β)
        ( λ γ →
          Σ ( map-codomain-lift-hom-arrow f g h α β γ ~ δ)
            ( λ Hi → coh-codomain-lift-hom-arrow f g h α β γ ∙h β₁ ·l Hi ~ Hδ))
      by
        equiv-tot
          ( λ γ →
            extensionality-lift
              ( map-codomain-hom-arrow g h β)
              ( map-codomain-hom-arrow f h α)
              ( lift-codomain-lift-hom-arrow f g h α β γ)
              ( δ , Hδ))
    ≃ Σ ( Σ (A' → B') (_~ δ))
        ( λ (i , Hi) →
          Σ ( Σ ( coherence-triangle-maps
                  ( map-codomain-hom-arrow f h α)
                  ( map-codomain-hom-arrow g h β)
                  ( i))
                ( λ I → I ∙h β₁ ·l Hi ~ Hδ))
            ( λ (I , HI) → lift-hom-arrow-of-lift-codomain-hom-arrow (i , I)))
      by reassociate
    ≃ Σ ( Σ ( coherence-triangle-maps
              ( map-codomain-hom-arrow f h α)
              ( map-codomain-hom-arrow g h β)
              ( δ))
            ( λ I → I ∙h β₁ ·l refl-htpy ~ Hδ))
        ( λ (I , HI) → lift-hom-arrow-of-lift-codomain-hom-arrow (δ , I))
      by left-unit-law-Σ-is-contr (is-torsorial-htpy' δ) (δ , refl-htpy)
    ≃ Σ ( Σ ( coherence-triangle-maps
              ( map-codomain-hom-arrow f h α)
              ( map-codomain-hom-arrow g h β)
              ( δ))
            ( _~ Hδ))
        ( λ (I , HI) → lift-hom-arrow-of-lift-codomain-hom-arrow (δ , I))
      by
        equiv-Σ-equiv-base
          ( λ (I , HI) → lift-hom-arrow-of-lift-codomain-hom-arrow (δ , I))
          ( equiv-tot (λ I → equiv-concat-htpy inv-htpy-right-unit-htpy Hδ))
    ≃ lift-hom-arrow-of-lift-codomain-hom-arrow (δ , Hδ)
      by left-unit-law-Σ-is-contr (is-torsorial-htpy' Hδ) (Hδ , refl-htpy)
    where
      reassociate :
        Σ ( lift-hom-arrow f g h α β)
        ( λ γ →
          Σ ( map-codomain-lift-hom-arrow f g h α β γ ~ δ)
            ( λ Hi →
              coh-codomain-lift-hom-arrow f g h α β γ ∙h β₁ ·l Hi ~ Hδ)) ≃
        Σ ( Σ (A' → B') (_~ δ))
          ( λ (i , Hi) →
            Σ ( Σ ( coherence-triangle-maps
                    ( map-codomain-hom-arrow f h α)
                    ( map-codomain-hom-arrow g h β)
                    ( i))
                  ( λ I → I ∙h β₁ ·l Hi ~ Hδ))
                ( λ (I , HI) →
                  lift-hom-arrow-of-lift-codomain-hom-arrow (i , I)))
      reassociate =
        ( ( λ (((γ₀ , γ₁ , Hγ) , (Γ₀ , Γ₁ , HΓ)) , (Hi , HI)) →
            ( (γ₁ , Hi) , (Γ₁ , HI) , γ₀ , Hγ , Γ₀ , HΓ)) ,
          ( is-equiv-is-invertible
            ( λ ((γ₁ , Hi) , (Γ₁ , HI) , γ₀ , Hγ , Γ₀ , HΓ) →
              ((γ₀ , γ₁ , Hγ) , (Γ₀ , Γ₁ , HΓ)) , (Hi , HI))
            ( refl-htpy)
            ( refl-htpy)))
```

### Uniqueness of lifts of cartesian morphisms

Given a cartesian morphism of arrows, then lifts along lifts in the codomain are
unique.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (α : hom-arrow f h) (β : hom-arrow g h)
  (let β₁ = map-codomain-hom-arrow g h β)
  (let Hβ = coh-hom-arrow g h β)
  (let Hα = coh-hom-arrow f h α)
  ((i , I) : lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α))
  where

  equiv-htpy-cone-is-lift-hom-arrow-of-lift-codomain-hom-arrow :
    (j : A → B) →
    is-lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β (i , I) j ≃
    htpy-cone β₁ h
      ( g ∘ j , map-domain-hom-arrow g h β ∘ j , Hβ ·r j)
      ( i ∘ f , map-domain-hom-arrow f h α , inv-htpy I ·r f ∙h Hα)
  equiv-htpy-cone-is-lift-hom-arrow-of-lift-codomain-hom-arrow j =
    equiv-Σ _
      ( equiv-inv-htpy (i ∘ f) (g ∘ j))
      ( λ H →
        equiv-Σ _
          ( equiv-inv-htpy
            ( map-domain-hom-arrow f h α)
            ( map-domain-hom-arrow g h β ∘ j))
          ( λ J →
            equivalence-reasoning
            ( Hα ∙h h ·l J ~ I ·r f ∙h (β₁ ·l H ∙h Hβ ·r j))
            ≃ ( I ·r f ∙h (β₁ ·l H ∙h Hβ ·r j) ~ Hα ∙h h ·l J)
              by equiv-inv-htpy (Hα ∙h h ·l J) (I ·r f ∙h (β₁ ·l H ∙h Hβ ·r j))
            ≃ ( β₁ ·l H ∙h Hβ ·r j ~ inv-htpy I ·r f ∙h (Hα ∙h h ·l J))
              by
                equiv-left-transpose-htpy-concat
                  ( I ·r f)
                  ( β₁ ·l H ∙h Hβ ·r j)
                  ( Hα ∙h h ·l J)
            ≃ ( Hβ ·r j ~
                inv-htpy (β₁ ·l H) ∙h (inv-htpy I ·r f ∙h (Hα ∙h h ·l J)))
              by
                equiv-left-transpose-htpy-concat
                  ( β₁ ·l H)
                  ( Hβ ·r j)
                  ( inv-htpy I ·r f ∙h (Hα ∙h h ·l J))
            ≃ ( Hβ ·r j ~
                β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h (Hα ∙h h ·l J)))
              by
                equiv-tr
                  ( λ Q → Hβ ·r j ~ Q ∙h (inv-htpy I ·r f ∙h (Hα ∙h h ·l J)))
                  ( inv (eq-htpy (left-whisker-inv-htpy β₁ H)))
            ≃ ( Hβ ·r j ~
                ( β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα)) ∙h h ·l J)
              by
                equiv-tr
                  ( Hβ ·r j ~_)
                  ( ( ap
                      ( β₁ ·l (inv-htpy H) ∙h_)
                      ( eq-htpy
                        ( inv-htpy-assoc-htpy (inv-htpy I ·r f) Hα (h ·l J)))) ∙
                    ( eq-htpy
                      ( inv-htpy-assoc-htpy
                        ( β₁ ·l (inv-htpy H))
                        ( inv-htpy I ·r f ∙h Hα)
                        ( h ·l J))))
            ≃ ( Hβ ·r j ∙h inv-htpy (h ·l J) ~
                β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα))
              by
                equiv-right-transpose-htpy-concat'
                  ( Hβ ·r j)
                  ( β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα))
                  ( h ·l J)
            ≃ ( Hβ ·r j ∙h h ·l inv-htpy J ~
                β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα))
              by
                equiv-tr
                  ( λ Q →
                    Hβ ·r j ∙h Q ~ β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα))
                  ( inv (eq-htpy (left-whisker-inv-htpy h J)))))

  abstract
    uniqueness-lift-map-codomain-is-cartesian-hom-arrow :
      is-cartesian-hom-arrow g h β →
      is-torsorial
        ( is-lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β (i , I))
    uniqueness-lift-map-codomain-is-cartesian-hom-arrow H =
      is-contr-equiv _
        ( equiv-tot
          ( equiv-htpy-cone-is-lift-hom-arrow-of-lift-codomain-hom-arrow))
        ( uniqueness-universal-property-pullback β₁ h
          ( cone-hom-arrow g h β)
          ( up-pullback-cartesian-hom-arrow g h (β , H))
          ( A)
          ( i ∘ f , map-domain-hom-arrow f h α , inv-htpy I ·r f ∙h Hα))
```

<!-- This uniqueness proof also constructs an explicit lift, making the entire next section purposeless -->

> What follows is another computation of the same. Should be deleted.

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

  abstract
    uniqueness-lift-map-codomain-cartesian-hom-arrow' :
      is-torsorial
        ( λ (j : A → B) →
          Σ ( coherence-hom-arrow f g j i)
            ( λ J →
              Σ ( coherence-triangle-maps'
                  ( map-domain-hom-arrow f h α)
                  ( map-domain-cartesian-hom-arrow g h β)
                  ( j))
                ( λ K →
                  coherence-htpy-hom-arrow f h
                    ( comp-hom-arrow f g h
                      ( hom-arrow-cartesian-hom-arrow g h β)
                      ( j , i , J))
                    ( α)
                    ( K)
                    ( H))))
    uniqueness-lift-map-codomain-cartesian-hom-arrow' =
      is-contr-equiv _
        ( equiv-tot
          ( λ j →
            equiv-Σ _
              ( equiv-inv-htpy (i ∘ f) (g ∘ j))
              ( λ J →
                equiv-tot
                  ( λ K →
                    equivalence-reasoning
                    ( ( map-codomain-cartesian-hom-arrow g h β ·l J) ∙h
                      ( coh-cartesian-hom-arrow g h β ·r j) ∙h
                      ( h ·l K) ~
                      ( H ·r f) ∙h
                      ( coh-hom-arrow f h α))
                    ≃ ( ( map-codomain-cartesian-hom-arrow g h β ·l J) ∙h
                        ( ( coh-cartesian-hom-arrow g h β ·r j) ∙h
                          ( h ·l K)) ~
                        ( H ·r f) ∙h
                        ( coh-hom-arrow f h α))
                      by
                        equiv-tr
                          ( λ Q → Q ~ ( H ·r f) ∙h ( coh-hom-arrow f h α))
                          ( eq-htpy
                            ( assoc-htpy
                              ( map-codomain-cartesian-hom-arrow g h β ·l J)
                              ( coh-cartesian-hom-arrow g h β ·r j)
                              ( h ·l K)))
                    ≃ ( ( coh-cartesian-hom-arrow g h β ·r j) ∙h (h ·l K) ~
                        ( inv-htpy
                          ( map-codomain-cartesian-hom-arrow g h β ·l J)) ∙h
                        ( ( H ·r f) ∙h (coh-hom-arrow f h α)))
                      by
                        equiv-left-transpose-htpy-concat
                          ( map-codomain-cartesian-hom-arrow g h β ·l J)
                          ( ( coh-cartesian-hom-arrow g h β ·r j) ∙h (h ·l K))
                          ( ( H ·r f) ∙h (coh-hom-arrow f h α))
                    ≃ ( ( coh-cartesian-hom-arrow g h β ·r j) ∙h (h ·l K) ~
                        ( ( map-codomain-cartesian-hom-arrow g h β) ·l
                          ( inv-htpy J)) ∙h
                        ( ( H ·r f) ∙h (coh-hom-arrow f h α)))
                      by
                        equiv-tr
                          ( λ Q →
                            (coh-cartesian-hom-arrow g h β ·r j) ∙h (h ·l K) ~
                            Q ∙h ((H ·r f) ∙h (coh-hom-arrow f h α)))
                          ( inv
                            ( eq-htpy
                              ( left-whisker-inv-htpy
                                ( map-codomain-cartesian-hom-arrow g h β)
                                ( J))))))))
        ( uniqueness-universal-property-pullback
          ( map-codomain-cartesian-hom-arrow g h β)
          ( h)
          ( cone-cartesian-hom-arrow g h β)
          ( up-pullback-cartesian-hom-arrow g h β)
          ( A)
          ( i ∘ f , pr1 α , H ·r f ∙h coh-hom-arrow f h α))
```

### Lifting cartesian morphisms along lifts of the codomain

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

We begin by constructing the commuting triangle of morphisms of arrows:

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

Now, if `α` was cartesian to begin with, the lift is also.

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
