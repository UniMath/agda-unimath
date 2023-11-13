# Epimorphisms with respect to maps into sets

```agda
module foundation.epimorphisms-with-respect-to-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.epimorphisms-with-respect-to-truncated-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.truncation-levels
open import foundation-core.univalence
```

</details>

## Idea

An epimorphism with respect to maps into sets are maps `f : A → B` suc that for
every set `C` the precomposition function `(B → C) → (A → C)` is an embedding.

## Definition

```agda
is-epimorphism-Set :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) → UUω
is-epimorphism-Set f =
  is-epimorphism-Truncated-Type zero-𝕋 f
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
        eq-htpy (λ b →
          apply-universal-property-trunc-Prop
            ( H b)
            ( Id-Prop C (g b) (h b))
            ( λ u →
              ( inv (ap g (pr2 u))) ∙
              ( ( htpy-eq p (pr1 u)) ∙
                ( ap h (pr2 u))))))
```

### Maps that are epimorphisms with respect to maps into sets are surjective

```agda
abstract
  is-surjective-is-epimorphism-Set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-epimorphism-Set f → is-surjective f
  is-surjective-is-epimorphism-Set {l1} {l2} {A} {B} {f} H b =
    map-equiv
      ( equiv-eq
        ( ap
          ( pr1)
          ( htpy-eq
            ( is-injective-is-emb
              ( H (Prop-Set (l1 ⊔ l2)))
              { g}
              { h}
              ( eq-htpy
                ( λ a →
                  eq-iff
                    ( λ _ → unit-trunc-Prop (pair a refl))
                    ( λ _ → raise-star))))
            ( b))))
      ( raise-star)
    where
    g : B → Prop (l1 ⊔ l2)
    g y = raise-unit-Prop (l1 ⊔ l2)
    h : B → Prop (l1 ⊔ l2)
    h y = ∃-Prop A (λ x → f x ＝ y)
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
