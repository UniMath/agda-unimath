# Functoriality of W-types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module trees.functoriality-w-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types funext univalence
open import foundation.contractible-maps funext
open import foundation.dependent-pair-types
open import foundation.dependent-products-truncated-types funext
open import foundation.embeddings funext
open import foundation.equivalences funext
open import foundation.fibers-of-maps funext
open import foundation.function-types funext
open import foundation.functoriality-dependent-function-types funext univalence
open import foundation.functoriality-dependent-pair-types funext
open import foundation.identity-types funext
open import foundation.propositional-maps funext
open import foundation.transport-along-identifications
open import foundation.truncated-maps funext
open import foundation.truncated-types funext univalence
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice funext
open import foundation.universe-levels

open import trees.w-types funext univalence truncations
```

</details>

## Idea

The W-type constructor acts functorially on `A` and `B`. It is covariant in `A`,
and contravariant in `B`.

## Definition

```agda
map-𝕎' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (g : (x : A) → D (f x) → B x) →
  𝕎 A B → 𝕎 C D
map-𝕎' D f g (tree-𝕎 a α) = tree-𝕎 (f a) (λ d → map-𝕎' D f g (α (g a d)))

map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  𝕎 A B → 𝕎 C D
map-𝕎 D f e = map-𝕎' D f (λ x → map-inv-equiv (e x))
```

## Properties

### We compute the fibers of `map-𝕎`

```agda
fiber-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  𝕎 C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
fiber-map-𝕎 D f e (tree-𝕎 c γ) =
  (fiber f c) × ((d : D c) → fiber (map-𝕎 D f e) (γ d))

abstract
  equiv-fiber-map-𝕎 :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3}
    (D : C → UU l4) (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
    (y : 𝕎 C D) → fiber (map-𝕎 D f e) y ≃ fiber-map-𝕎 D f e y
  equiv-fiber-map-𝕎 {A = A} {B} {C} D f e (tree-𝕎 c γ) =
    ( ( ( inv-equiv
          ( associative-Σ A
            ( λ a → f a ＝ c)
            ( λ t → (d : D c) → fiber (map-𝕎 D f e) (γ d)))) ∘e
        ( equiv-tot
          ( λ a →
            ( ( equiv-tot
                ( λ p →
                  ( ( equiv-Π
                      ( λ (d : D c) → fiber (map-𝕎 D f e) (γ d))
                      ( (equiv-tr D p) ∘e (e a))
                      ( λ b → id-equiv)) ∘e
                    ( inv-distributive-Π-Σ)) ∘e
                  ( equiv-tot
                    ( λ α →
                      equiv-Π
                        ( λ (b : B a) →
                          map-𝕎 D f e (α b) ＝ γ (tr D p (map-equiv (e a) b)))
                        ( inv-equiv (e a))
                        ( λ d →
                          ( equiv-concat'
                            ( map-𝕎 D f e
                              ( α (map-inv-equiv (e a) d)))
                            ( ap
                              ( γ ∘ (tr D p))
                              ( inv (is-section-map-inv-equiv (e a) d)))) ∘e
                          ( inv-equiv
                            ( equiv-Eq-𝕎-eq
                              ( map-𝕎 D f e
                                ( α (map-inv-equiv (e a) d)))
                              ( γ (tr D p d))))))))) ∘e
              ( equiv-left-swap-Σ)) ∘e
            ( equiv-tot
              ( λ α →
                equiv-Eq-𝕎-eq
                  ( tree-𝕎
                    ( f a)
                    ( ( map-𝕎 D f e) ∘
                      ( α ∘ map-inv-equiv (e a)))) (tree-𝕎 c γ)))))) ∘e
      ( associative-Σ A
        ( λ a → B a → 𝕎 A B)
        ( λ t → map-𝕎 D f e (structure-𝕎-Alg t) ＝ tree-𝕎 c γ))) ∘e
    ( equiv-Σ
      ( λ t → map-𝕎 D f e (structure-𝕎-Alg t) ＝ tree-𝕎 c γ)
      ( inv-equiv-structure-𝕎-Alg)
      ( λ x →
        equiv-concat
          ( ap (map-𝕎 D f e) (is-section-map-inv-structure-𝕎-Alg x))
          ( tree-𝕎 c γ)))
```

### For any family of equivalences `e` over `f`, if `f` is truncated then `map-𝕎 f e` is truncated

```agda
is-trunc-map-map-𝕎 :
  {l1 l2 l3 l4 : Level} (k : 𝕋)
  {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-trunc-map k f → is-trunc-map k (map-𝕎 D f e)
is-trunc-map-map-𝕎 k D f e H (tree-𝕎 c γ) =
  is-trunc-equiv k
    ( fiber-map-𝕎 D f e (tree-𝕎 c γ))
    ( equiv-fiber-map-𝕎 D f e (tree-𝕎 c γ))
    ( is-trunc-Σ
      ( H c)
      ( λ t → is-trunc-Π k (λ d → is-trunc-map-map-𝕎 k D f e H (γ d))))
```

### For any family of equivalences `e` over `f`, if `f` is an equivalence then `map-𝕎 f e` is an equivalence

```agda
is-equiv-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-equiv f → is-equiv (map-𝕎 D f e)
is-equiv-map-𝕎 D f e H =
  is-equiv-is-contr-map
    ( is-trunc-map-map-𝕎 neg-two-𝕋 D f e (is-contr-map-is-equiv H))

equiv-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A ≃ C) (e : (x : A) → B x ≃ D (map-equiv f x)) →
  𝕎 A B ≃ 𝕎 C D
equiv-𝕎 D f e =
  pair
    ( map-𝕎 D (map-equiv f) e)
    ( is-equiv-map-𝕎 D (map-equiv f) e (is-equiv-map-equiv f))
```

### For any family of equivalences `e` over `f`, if `f` is an embedding, then `map-𝕎 f e` is an embedding

```agda
is-emb-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-emb f → is-emb (map-𝕎 D f e)
is-emb-map-𝕎 D f e H =
  is-emb-is-prop-map
    (is-trunc-map-map-𝕎 neg-one-𝕋 D f e (is-prop-map-is-emb H))

emb-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A ↪ C) (e : (x : A) → B x ≃ D (map-emb f x)) → 𝕎 A B ↪ 𝕎 C D
emb-𝕎 D f e =
  pair
    ( map-𝕎 D (map-emb f) e)
    ( is-emb-map-𝕎 D (map-emb f) e (is-emb-map-emb f))
```
