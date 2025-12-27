### The derivative of `cf` is `cf'`

```agda
module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (f' : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  (is-derivative-f-f' :
    is-derivative-real-function-proper-closed-interval-ℝ [a,b] f f')
  (c : ℝ l3)
  where

  abstract
    is-derivative-scalar-mul-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( λ x → c *ℝ f x)
        ( λ x → c *ℝ f' x)
    is-derivative-scalar-mul-real-function-proper-closed-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( λ x → c *ℝ f x)
              ( λ x → c *ℝ f' x))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (μ , is-mod-μ) ← is-derivative-f-f'
        (q , |c|<q) ← exists-ℚ⁺-le-ℝ⁰⁺ (nonnegative-abs-ℝ c)
        is-derivative-modulus-of-real-function-proper-closed-interval-ℝ [a,b]
          ( _)
          ( _)
          ( λ ε →
            ( μ (ε *ℚ⁺ inv-ℚ⁺ q) ,
              λ x y N⟨ε/q⟩xy →
              chain-of-inequalities
                dist-ℝ (c *ℝ f y -ℝ c *ℝ f x) (c *ℝ f' x *ℝ (pr1 y -ℝ pr1 x))
                ≤ dist-ℝ (c *ℝ (f y -ℝ f x)) (c *ℝ (f' x *ℝ (pr1 y -ℝ pr1 x)))
                  by
                    leq-eq-ℝ
                      ( ap-dist-ℝ
                        ( inv (left-distributive-mul-diff-ℝ _ _ _))
                        ( associative-mul-ℝ _ _ _))
                ≤ abs-ℝ c *ℝ dist-ℝ (f y -ℝ f x) (f' x *ℝ (pr1 y -ℝ pr1 x))
                  by leq-eq-ℝ (inv (left-distributive-abs-mul-dist-ℝ _ _ _))
                ≤ ( real-ℚ⁺ q) *ℝ
                  ( real-ℚ⁺ (ε *ℚ⁺ inv-ℚ⁺ q) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    preserves-leq-mul-ℝ⁰⁺
                      ( nonnegative-abs-ℝ c)
                      ( nonnegative-real-ℚ⁺ q)
                      ( nonnegative-dist-ℝ _ _)
                      ( nonnegative-real-ℚ⁺ (ε *ℚ⁺ inv-ℚ⁺ q) *ℝ⁰⁺
                        nonnegative-dist-ℝ _ _)
                      ( leq-le-ℝ |c|<q)
                      ( is-mod-μ
                        ( ε *ℚ⁺ inv-ℚ⁺ q)
                        ( x)
                        ( y)
                        ( N⟨ε/q⟩xy))
                ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                  by
                    leq-eq-ℝ
                      ( ( inv (associative-mul-ℝ _ _ _)) ∙
                        ( ap-mul-ℝ
                          ( ( mul-real-ℚ _ _) ∙
                            ( ap
                              ( real-ℚ⁺)
                              ( is-identity-right-conjugation-Ab
                                ( abelian-group-mul-ℚ⁺)
                                ( q)
                                ( ε))))
                          ( refl)))))
```
