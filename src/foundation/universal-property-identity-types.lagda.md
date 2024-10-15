# The universal property of identity types

```agda
module foundation.universal-property-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.preunivalence
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The **universal property of identity types** characterizes families of maps out
of the [identity type](foundation-core.identity-types.md). This universal
property is also known as the **type theoretic Yoneda lemma**.

## Theorem

```agda
ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → a ＝ x → UU l2} →
  ((x : A) (p : a ＝ x) → B x p) → B a refl
ev-refl a f = f a refl

ev-refl' :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → x ＝ a → UU l2} →
  ((x : A) (p : x ＝ a) → B x p) → B a refl
ev-refl' a f = f a refl

abstract
  is-equiv-ev-refl :
    {l1 l2 : Level} {A : UU l1} (a : A)
    {B : (x : A) → a ＝ x → UU l2} → is-equiv (ev-refl a {B})
  is-equiv-ev-refl a =
    is-equiv-is-invertible
      ( ind-Id a _)
      ( λ b → refl)
      ( λ f → eq-htpy
        ( λ x → eq-htpy
          ( ind-Id a
            ( λ x' p' → ind-Id a _ (f a refl) x' p' ＝ f x' p')
            ( refl) x)))

equiv-ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → a ＝ x → UU l2} →
  ((x : A) (p : a ＝ x) → B x p) ≃ (B a refl)
pr1 (equiv-ev-refl a) = ev-refl a
pr2 (equiv-ev-refl a) = is-equiv-ev-refl a

equiv-ev-refl' :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → x ＝ a → UU l2} →
  ((x : A) (p : x ＝ a) → B x p) ≃ B a refl
equiv-ev-refl' a {B} =
  ( equiv-ev-refl a) ∘e
  ( equiv-Π-equiv-family (λ x → equiv-precomp-Π (equiv-inv a x) (B x)))

is-equiv-ev-refl' :
  {l1 l2 : Level} {A : UU l1} (a : A)
  {B : (x : A) → x ＝ a → UU l2} → is-equiv (ev-refl' a {B})
is-equiv-ev-refl' a = is-equiv-map-equiv (equiv-ev-refl' a)
```

### The type of fiberwise maps from `Id a` to a torsorial type family `B` is equivalent to the type of fiberwise equivalences

Note that the type of fiberwise equivalences is a
[subtype](foundation-core.subtypes.md) of the type of fiberwise maps. By the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md),
it is a [full subtype](foundation.full-subtypes.md), hence it is equivalent to
the whole type of fiberwise maps.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (a : A) {B : A → UU l2}
  (is-torsorial-B : is-torsorial B)
  where

  equiv-fam-map-fam-equiv-is-torsorial :
    ((x : A) → (a ＝ x) ≃ B x) ≃ ((x : A) → (a ＝ x) → B x)
  equiv-fam-map-fam-equiv-is-torsorial =
    ( equiv-inclusion-is-full-subtype
      ( λ h → Π-Prop A (λ a → is-equiv-Prop (h a)))
      ( fundamental-theorem-id is-torsorial-B)) ∘e
    ( equiv-fiberwise-equiv-fam-equiv _ _)
```

### `Id : A → (A → 𝒰)` is an embedding

We first show that [the preunivalence axiom](foundation.preunivalence.md)
implies that the map `Id : A → (A → 𝒰)` is an
[embedding](foundation.embeddings.md). Since the
[univalence axiom](foundation.univalence.md) implies preunivalence, it follows
that `Id : A → (A → 𝒰)` is an embedding under the postulates of agda-unimath.

#### Preunivalence implies that `Id : A → (A → 𝒰)` is an embedding

The proof that preunivalence implies that `Id : A → (A → 𝒰)` is an embedding
proceeds via the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md)
by showing that the [fiber](foundation.fibers-of-maps.md) of `Id` at `Id a` is
[contractible](foundation.contractible-types.md) for each `a : A`. To see this,
we first note that this fiber has an element `(a , refl)`. Therefore it suffices
to show that this fiber is a proposition. We do this by constructing an
embedding

```text
  fiber Id (Id a) ↪ Σ A (Id a).
```

Since the codomain of this embedding is contractible, the claim follows. The
above embedding is constructed as the composite of the following embeddings

```text
  Σ (x : A), Id x ＝ Id a
    ↪ Σ (x : A), (y : A) → (x ＝ y) ＝ (a ＝ y)
    ↪ Σ (x : A), (y : A) → (x ＝ y) ≃ (a ＝ y)
    ↪ Σ (x : A), Σ (e : (y : A) → (x ＝ y) → (a ＝ y)), (y : A) → is-equiv (e y)
    ↪ Σ (x : A), (y : A) → (x ＝ y) → (a ＝ y)
    ↪ Σ (x : A), a ＝ x.
```

In this composite, we used preunivalence at the second step.

```agda
module _
  {l : Level} (A : UU l)
  (L : (a x y : A) → instance-preunivalence (Id x y) (Id a y))
  where

  emb-fiber-Id-preunivalent-Id :
    (a : A) → fiber' Id (Id a) ↪ Σ A (Id a)
  emb-fiber-Id-preunivalent-Id a =
    comp-emb
      ( comp-emb
        ( emb-equiv
          ( equiv-tot
            ( λ x →
              ( equiv-ev-refl x) ∘e
              ( equiv-fam-map-fam-equiv-is-torsorial x (is-torsorial-Id a)))))
        ( emb-tot
          ( λ x →
            comp-emb
              ( emb-Π (λ y → _ , L a x y))
              ( emb-equiv equiv-funext))))
      ( emb-equiv (inv-equiv (equiv-fiber Id (Id a))))

  is-emb-Id-preunivalent-Id : is-emb (Id {A = A})
  is-emb-Id-preunivalent-Id a =
    fundamental-theorem-id
      ( ( a , refl) ,
        ( λ _ →
          is-injective-emb
            ( emb-fiber-Id-preunivalent-Id a)
            ( eq-is-contr (is-torsorial-Id a))))
      ( λ _ → ap Id)

module _
  (L : preunivalence-axiom) {l : Level} (A : UU l)
  where

  is-emb-Id-preunivalence-axiom : is-emb (Id {A = A})
  is-emb-Id-preunivalence-axiom =
    is-emb-Id-preunivalent-Id A (λ a x y → L (Id x y) (Id a y))
```

#### `Id : A → (A → 𝒰)` is an embedding

```agda
module _
  {l : Level} (A : UU l)
  where

  is-emb-Id : is-emb (Id {A = A})
  is-emb-Id = is-emb-Id-preunivalence-axiom preunivalence A
```

#### For any type family `B` over `A`, the type of pairs `(a , e)` consisting of `a : A` and a family of equivalences `e : (x : A) → (a ＝ x) ≃ B x` is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-proof-irrelevant-total-family-of-equivalences-Id :
    is-proof-irrelevant (Σ A (λ a → (x : A) → (a ＝ x) ≃ B x))
  is-proof-irrelevant-total-family-of-equivalences-Id (a , e) =
    is-contr-equiv
      ( Σ A (λ b → (x : A) → (b ＝ x) ≃ (a ＝ x)))
      ( equiv-tot
        ( λ b →
          equiv-Π-equiv-family
            ( λ x → equiv-postcomp-equiv (inv-equiv (e x)) (b ＝ x))))
      ( is-contr-equiv'
        ( fiber Id (Id a))
        ( equiv-tot
          ( λ b →
            equiv-Π-equiv-family (λ x → equiv-univalence) ∘e equiv-funext))
        ( is-proof-irrelevant-is-prop
          ( is-prop-map-is-emb (is-emb-Id A) (Id a))
          ( a , refl)))

  is-prop-total-family-of-equivalences-Id :
    is-prop (Σ A (λ a → (x : A) → (a ＝ x) ≃ B x))
  is-prop-total-family-of-equivalences-Id =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-total-family-of-equivalences-Id)
```

### The type of point-preserving fiberwise equivalences between `Id x` and a pointed torsorial type family is contractible

**Proof:** Since `ev-refl` is an equivalence, it follows that its fibers are
contractible. Explicitly, given a point `b : B a`, the type of maps
`h : (x : A) → (a = x) → B x` such that `h a refl = b` is contractible. But the
type of fiberwise maps is equivalent to the type of fiberwise equivalences.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a : A} {B : A → UU l2} (b : B a)
  (is-torsorial-B : is-torsorial B)
  where

  abstract
    is-torsorial-pointed-fam-equiv-is-torsorial :
      is-torsorial
        ( λ (e : (x : A) → (a ＝ x) ≃ B x) →
          map-equiv (e a) refl ＝ b)
    is-torsorial-pointed-fam-equiv-is-torsorial =
      is-contr-equiv'
        ( fiber (ev-refl a {B = λ x _ → B x}) b)
        ( equiv-Σ _
          ( inv-equiv
            ( equiv-fam-map-fam-equiv-is-torsorial a is-torsorial-B))
          ( λ h →
            equiv-inv-concat
              ( inv
                ( ap
                  ( ev-refl a)
                  ( is-section-map-inv-equiv
                    ( equiv-fam-map-fam-equiv-is-torsorial a is-torsorial-B)
                    ( h))))
              ( b)))
        ( is-contr-map-is-equiv
          ( is-equiv-ev-refl a)
          ( b))
```

## See also

- In
  [`foundation.torsorial-type-families`](foundation.torsorial-type-families.md)
  we will show that the fiber of `Id : A → (A → 𝒰)` at `B : A → 𝒰` is equivalent
  to `is-torsorial B`.

## References

- The fact that preunivalence, or axiom L, is sufficient to prove that
  `Id : A → (A → 𝒰)` is an embedding was first observed and formalized by Martín
  Escardó,
  [https://www.cs.bham.ac.uk//~mhe/TypeTopology/UF.IdEmbedding.html](https://www.cs.bham.ac.uk//~mhe/TypeTopology/UF.IdEmbedding.html).

{{#bibliography}} {{#reference TypeTopology}}
