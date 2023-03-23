# Binary functoriality of set quotients

```agda
module foundation.cartesian-products-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies
open import foundation.exponents-set-quotients
open import foundation.function-extensionality
open import foundation.functoriality-set-quotients
open import foundation.homotopies
open import foundation.identity-types
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.equality-cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients

open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.cartesian-product-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.propositions
open import foundation-core.subtype-identity-principle
open import foundation-core.subtypes
open import foundation-core.universe-levels
```

</details>

## Idea

Given two types `A` and `B`, equipped with equivalence relations `R` and
`S`, respectively, the cartesian product of their set quotients is the
set quotient of their product

## Definition

### Binary hom of equivalence relation

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU l3} (S : Eq-Rel l4 B)
  where

  prod-Eq-Rel :
    Eq-Rel (l2 ⊔ l4) (A × B)
  prod-Eq-Rel =
    pair
      ( λ (a , b) (a' , b') →
        prod-Prop
          ( prop-Eq-Rel R a a')
          ( prop-Eq-Rel S b b'))
      ( pair
        ( pair
          ( refl-Eq-Rel R )
          ( refl-Eq-Rel S ))
        ( pair
          ( λ (p , q) →
            pair
              ( symm-Eq-Rel R p)
              ( symm-Eq-Rel S q))
          ( λ (p , q) (p' , q') →
            pair
              ( trans-Eq-Rel R p p')
              ( trans-Eq-Rel S q q'))))

  prod-set-quotient-Set : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  prod-set-quotient-Set = prod-Set (quotient-Set R) (quotient-Set S)

  prod-set-quotient : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  prod-set-quotient = pr1 prod-set-quotient-Set

  is-set-prod-set-quotient : is-set prod-set-quotient
  is-set-prod-set-quotient = pr2 prod-set-quotient-Set

  prod-set-quotient-map : (A × B) → prod-set-quotient
  prod-set-quotient-map (a , b) =
    pair (quotient-map R a) (quotient-map S b)

  reflecting-map-prod-quotient-map :
    reflecting-map-Eq-Rel prod-Eq-Rel prod-set-quotient
  reflecting-map-prod-quotient-map =
    pair
      prod-set-quotient-map
      ( λ (p , q) →
        ( eq-pair
          ( apply-effectiveness-quotient-map' R p)
          ( apply-effectiveness-quotient-map' S q)))

  inv-precomp-set-quotient-prod-set-quotient :
    {l : Level}
    (X : Set l) →
    reflecting-map-Eq-Rel prod-Eq-Rel (type-Set X) →
    type-hom-Set prod-set-quotient-Set X
  inv-precomp-set-quotient-prod-set-quotient X (f , H) (qa , qb) =
    inv-precomp-set-quotient
      ( R)
      ( hom-Set (quotient-Set S) X)
      ( pair
        ( λ a qb' →
          inv-precomp-set-quotient S X
            ( pair
              (λ b → f (a , b))
              (λ p → H (pair (refl-Eq-Rel R) p)))
            qb')
        ( λ {a1} {a2} p →
          ( ap (inv-precomp-set-quotient S X)
            ( eq-pair-Σ
              (eq-htpy (λ b → H (pair p (refl-Eq-Rel S))))
              ( eq-is-prop'
                ( is-prop-reflects-Eq-Rel S X _ ) _ _)))))
      ( qa) ( qb)

  is-set-quotient-prod-set-quotient :
    { l : Level} →
    ( is-set-quotient l
      prod-Eq-Rel
      prod-set-quotient-Set
      reflecting-map-prod-quotient-map)
  is-set-quotient-prod-set-quotient X =
    pair
      ( pair
        ( inv-precomp-set-quotient-prod-set-quotient X)
        ( λ (f , H) →
          eq-pair-Σ
            ( eq-htpy
              ( λ (a , b) →
                ( htpy-eq
                  ( issec-inv-precomp-set-quotient R
                    ( hom-Set (quotient-Set S) X) _ a)
                  ( quotient-map S b) ∙
                ( issec-inv-precomp-set-quotient S X _ b))))
           ( eq-is-prop'
             ( is-prop-reflects-Eq-Rel prod-Eq-Rel X f) _ _)))
      ( pair
        ( inv-precomp-set-quotient-prod-set-quotient X)
        ( λ f →
          ( eq-htpy
            ( λ (qa , qb) →
              htpy-eq (htpy-eq (lemma f ∙ lemma3 f) qa) qb))))
    where
    module _
      (F  : type-hom-Set prod-set-quotient-Set X)
      where
      f : A × B → type-Set X
      f = pr1 (precomp-Set-Quotient
          prod-Eq-Rel
          prod-set-quotient-Set
          reflecting-map-prod-quotient-map X F)
      H : reflects-Eq-Rel prod-Eq-Rel f
      H = pr2 (precomp-Set-Quotient
          prod-Eq-Rel
          prod-set-quotient-Set
          reflecting-map-prod-quotient-map X F)
      mapB :
        ( a : A ) →
        reflecting-map-Eq-Rel S (type-Set X)
      mapB a =
        ( pair
            (λ b → f (a , b))
            (λ p → H (pair (refl-Eq-Rel R) p)))
      lemma1 :
        ( a : A ) →
        ( mapB a) ＝
         ( precomp-Set-Quotient S
           ( quotient-Set S)
           ( reflecting-map-quotient-map S)
           ( X)
           ( λ qb → F (quotient-map R a , qb)))
      lemma1 a =
        eq-pair-Σ refl
          (eq-is-prop' ( is-prop-reflects-Eq-Rel S X _ ) _ _ )
      lemma2 :
        ( pair
          ( λ a qb' →
            inv-precomp-set-quotient S X
              ( pair
                (λ b → f (a , b))
                (λ p → H (pair (refl-Eq-Rel R) p)))
              qb')
          ( λ {a1} {a2} p →
            ( ap (inv-precomp-set-quotient S X)
              ( eq-pair-Σ
                (eq-htpy (λ b → H (pair p (refl-Eq-Rel S))))
                ( eq-is-prop'
                  ( is-prop-reflects-Eq-Rel S X _ ) _ _))))) ＝
          ( precomp-Set-Quotient R
            ( quotient-Set R)
            ( reflecting-map-quotient-map R)
            ( hom-Set (quotient-Set S) X )
            ( λ qa qb → F (qa , qb)))
      lemma2 =
        eq-pair-Σ
          (eq-htpy λ a → ap (inv-precomp-set-quotient S X) (lemma1 a) ∙
            isretr-inv-precomp-set-quotient S X _ )
          ((eq-is-prop' (is-prop-reflects-Eq-Rel R (( hom-Set (quotient-Set S) X ) ) _ ) _ _ ) )
      lemma :
        inv-precomp-set-quotient
          ( R)
          ( hom-Set (quotient-Set S) X)
          ( pair
            ( λ a qb' →
              inv-precomp-set-quotient S X
                ( pair
                  (λ b → f (a , b))
                  (λ p → H (pair (refl-Eq-Rel R) p)))
                qb')
            ( λ {a1} {a2} p →
              ( ap (inv-precomp-set-quotient S X)
                ( eq-pair-Σ
                  (eq-htpy (λ b → H (pair p (refl-Eq-Rel S))))
                  ( eq-is-prop'
                    ( is-prop-reflects-Eq-Rel S X _ ) _ _)))))
           ＝
        inv-precomp-set-quotient
          ( R)
          ( hom-Set (quotient-Set S) X)
          ( precomp-Set-Quotient R
            ( quotient-Set R)
            ( reflecting-map-quotient-map R)
            ( hom-Set (quotient-Set S) X )
            ( λ qa qb → F (qa , qb)))
      lemma =
       ap
        (inv-precomp-set-quotient
          ( R)
          ( hom-Set (quotient-Set S) X)) (lemma2 )
      lemma3 :
        inv-precomp-set-quotient
          ( R)
          ( hom-Set (quotient-Set S) X)
          ( precomp-Set-Quotient R
            ( quotient-Set R)
            ( reflecting-map-quotient-map R)
            ( hom-Set (quotient-Set S) X )
            ( λ qa qb → F (qa , qb)))
         ＝ λ qa₁ qb₁ → F (qa₁ , qb₁)
      lemma3 = isretr-inv-precomp-set-quotient
          R ( hom-Set (quotient-Set S) X)
          ( λ qa qb → F (qa , qb))
          
        

  quotient-prod : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  quotient-prod = quotient-Set prod-Eq-Rel
```
