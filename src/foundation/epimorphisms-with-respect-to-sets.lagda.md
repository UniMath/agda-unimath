# Epimorphisms with respect to maps into sets

```agda
module foundation.epimorphisms-with-respect-to-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.precomposition-functions
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.univalence
```

</details>

## Idea

An epimorphism with respect to maps into sets are maps `f : A → B` such that for
every set `C` the precomposition function `(B → C) → (A → C)` is an embedding.

## Definition

```agda
is-epimorphism-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) → UUω
is-epimorphism-Set f =
  {l : Level} (C : Set l) → is-emb (precomp f (type-Set C))
```

## Properties

### Surjective maps are epimorphisms with respect to maps into sets

```agda
abstract
  is-epimorphism-is-surjective-Set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-surjective f → is-epimorphism-Set f
  is-epimorphism-is-surjective-Set H C =
    is-emb-is-injective
      ( is-set-function-type (is-set-type-Set C))
      ( λ {g} {h} p →
        eq-htpy
          ( λ b →
            apply-universal-property-trunc-Prop
              ( H b)
              ( Id-Prop C (g b) (h b))
              ( λ u →
                ( inv (ap g (pr2 u))) ∙
                ( htpy-eq p (pr1 u)) ∙
                ( ap h (pr2 u)))))
```

### Maps that are epimorphisms with respect to maps into sets are surjective

```agda
abstract
  is-surjective-is-epimorphism-Set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-epimorphism-Set f → is-surjective f
  is-surjective-is-epimorphism-Set {l1} {l2} {A} {B} {f} H b =
    map-eq
      ( ap
        ( pr1)
        ( htpy-eq
          ( is-injective-is-emb
            ( H (Prop-Set (l1 ⊔ l2)))
            { λ _ → raise-unit-Prop (l1 ⊔ l2)}
            { λ y → exists-structure-Prop A (λ x → f x ＝ y)}
            ( eq-htpy
              ( λ a →
                eq-iff
                  ( λ _ → unit-trunc-Prop (a , refl))
                  ( λ _ → raise-star))))
          ( b)))
      ( raise-star)
```

### There is at most one extension of a map into a set along a surjection

For any surjective map `f : A ↠ B` and any map `g : A → C` into a set `C`, the
type of extensions

```text
  Σ (B → C) (λ h → g ~ h ∘ f)
```

of `g` along `f` is a proposition. In
[The universal property of set quotients](foundation.universal-property-set-quotients.md)
we will show that this proposition is equivalent to the proposition

```text
  (a a' : A) → f a ＝ f a' → g a ＝ g a'.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  (C : Set l3) (g : A → type-Set C)
  where

  extension-along-surjection-Set : UU (l1 ⊔ l2 ⊔ l3)
  extension-along-surjection-Set =
    Σ (B → type-Set C) (λ h → g ~ h ∘ map-surjection f)

  abstract
    is-prop-extension-along-surjection-Set :
      is-prop extension-along-surjection-Set
    is-prop-extension-along-surjection-Set =
      is-prop-equiv'
        ( equiv-tot (λ h → equiv-funext ∘e equiv-inv _ g))
        ( is-prop-map-is-emb
          ( is-epimorphism-is-surjective-Set
            ( is-surjective-map-surjection f)
            ( C))
          ( g))
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
- [The universal property of set quotients](foundation.universal-property-set-quotients.md)
