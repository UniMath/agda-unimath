{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QinequalityZ45ZnaturalZ45Znumbers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- elementary-number-theory.inequality-natural-numbers.leq-ℕ
d_leq'45'ℕ_4 :: Integer -> Integer -> ()
d_leq'45'ℕ_4 = erased
-- elementary-number-theory.inequality-natural-numbers._≤-ℕ_
d__'8804''45'ℕ__14 :: Integer -> Integer -> ()
d__'8804''45'ℕ__14 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-ℕ'
d_leq'45'ℕ''_16 a0 a1 = ()
data T_leq'45'ℕ''_16
  = C_refl'45'leq'45'ℕ''_20 |
    C_propagate'45'leq'45'ℕ''_28 Integer T_leq'45'ℕ''_16
-- elementary-number-theory.inequality-natural-numbers.leq-zero-ℕ
d_leq'45'zero'45'ℕ_32 ::
  Integer -> MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4
d_leq'45'zero'45'ℕ_32 = erased
-- elementary-number-theory.inequality-natural-numbers.is-zero-leq-zero-ℕ
d_is'45'zero'45'leq'45'zero'45'ℕ_38 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'leq'45'zero'45'ℕ_38 = erased
-- elementary-number-theory.inequality-natural-numbers.is-zero-leq-zero-ℕ'
d_is'45'zero'45'leq'45'zero'45'ℕ''_42 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'leq'45'zero'45'ℕ''_42 = erased
-- elementary-number-theory.inequality-natural-numbers.succ-leq-ℕ
d_succ'45'leq'45'ℕ_46 :: Integer -> AgdaAny
d_succ'45'leq'45'ℕ_46 = erased
-- elementary-number-theory.inequality-natural-numbers.concatenate-eq-leq-eq-ℕ
d_concatenate'45'eq'45'leq'45'eq'45'ℕ_58 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_concatenate'45'eq'45'leq'45'eq'45'ℕ_58 = erased
-- elementary-number-theory.inequality-natural-numbers.concatenate-leq-eq-ℕ
d_concatenate'45'leq'45'eq'45'ℕ_68 ::
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_concatenate'45'leq'45'eq'45'ℕ_68 = erased
-- elementary-number-theory.inequality-natural-numbers.concatenate-eq-leq-ℕ
d_concatenate'45'eq'45'leq'45'ℕ_80 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny -> AgdaAny
d_concatenate'45'eq'45'leq'45'ℕ_80 = erased
-- elementary-number-theory.inequality-natural-numbers.is-decidable-leq-ℕ
d_is'45'decidable'45'leq'45'ℕ_90 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'leq'45'ℕ_90 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe (\ v3 -> v3))
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe d_is'45'decidable'45'leq'45'ℕ_90 (coe v2) (coe v3)
-- elementary-number-theory.inequality-natural-numbers.decide-leq-succ-ℕ
d_decide'45'leq'45'succ'45'ℕ_104 ::
  Integer ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_decide'45'leq'45'succ'45'ℕ_104 v0 v1 ~v2
  = du_decide'45'leq'45'succ'45'ℕ_104 v0 v1
du_decide'45'leq'45'succ'45'ℕ_104 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_decide'45'leq'45'succ'45'ℕ_104 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
                    (coe (\ v4 -> v4)) erased
                    (coe du_decide'45'leq'45'succ'45'ℕ_104 (coe v2) (coe v3))
-- elementary-number-theory.inequality-natural-numbers.refl-leq-ℕ
d_refl'45'leq'45'ℕ_124 :: Integer -> AgdaAny
d_refl'45'leq'45'ℕ_124 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-eq-ℕ
d_leq'45'eq'45'ℕ_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_leq'45'eq'45'ℕ_132 = erased
-- elementary-number-theory.inequality-natural-numbers.transitive-leq-ℕ
d_transitive'45'leq'45'ℕ_142 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_transitive'45'leq'45'ℕ_142 = erased
-- elementary-number-theory.inequality-natural-numbers.preserves-leq-succ-ℕ
d_preserves'45'leq'45'succ'45'ℕ_166 ::
  Integer -> Integer -> AgdaAny -> AgdaAny
d_preserves'45'leq'45'succ'45'ℕ_166 = erased
-- elementary-number-theory.inequality-natural-numbers.antisymmetric-leq-ℕ
d_antisymmetric'45'leq'45'ℕ_178 ::
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_antisymmetric'45'leq'45'ℕ_178 = erased
-- elementary-number-theory.inequality-natural-numbers.decide-leq-ℕ
d_decide'45'leq'45'ℕ_196 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_decide'45'leq'45'ℕ_196 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe d_decide'45'leq'45'ℕ_196 (coe v2) (coe v3)
-- elementary-number-theory.inequality-natural-numbers.preserves-order-add-ℕ
d_preserves'45'order'45'add'45'ℕ_212 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_preserves'45'order'45'add'45'ℕ_212 = erased
-- elementary-number-theory.inequality-natural-numbers.reflects-order-add-ℕ
d_reflects'45'order'45'add'45'ℕ_230 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_reflects'45'order'45'add'45'ℕ_230 = erased
-- elementary-number-theory.inequality-natural-numbers.preserves-order-mul-ℕ
d_preserves'45'order'45'mul'45'ℕ_248 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_preserves'45'order'45'mul'45'ℕ_248 = erased
-- elementary-number-theory.inequality-natural-numbers.preserves-order-mul-ℕ'
d_preserves'45'order'45'mul'45'ℕ''_270 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_preserves'45'order'45'mul'45'ℕ''_270 = erased
-- elementary-number-theory.inequality-natural-numbers.reflects-order-mul-ℕ
d_reflects'45'order'45'mul'45'ℕ_286 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_reflects'45'order'45'mul'45'ℕ_286 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-mul-ℕ
d_leq'45'mul'45'ℕ_306 :: Integer -> Integer -> AgdaAny
d_leq'45'mul'45'ℕ_306 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-mul-ℕ'
d_leq'45'mul'45'ℕ''_316 :: Integer -> Integer -> AgdaAny
d_leq'45'mul'45'ℕ''_316 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-mul-is-nonzero-ℕ
d_leq'45'mul'45'is'45'nonzero'45'ℕ_326 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_leq'45'mul'45'is'45'nonzero'45'ℕ_326 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-mul-is-nonzero-ℕ'
d_leq'45'mul'45'is'45'nonzero'45'ℕ''_350 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_leq'45'mul'45'is'45'nonzero'45'ℕ''_350 = erased
-- elementary-number-theory.inequality-natural-numbers.subtraction-leq-ℕ
d_subtraction'45'leq'45'ℕ_376 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_subtraction'45'leq'45'ℕ_376 v0 v1 ~v2
  = du_subtraction'45'leq'45'ℕ_376 v0 v1
du_subtraction'45'leq'45'ℕ_376 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_subtraction'45'leq'45'ℕ_376 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
             (coe v1) erased
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                (coe du_P_394 (coe v2) (coe v3)))
             erased
-- elementary-number-theory.inequality-natural-numbers._.P
d_P_394 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_P_394 v0 v1 ~v2 = du_P_394 v0 v1
du_P_394 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_P_394 v0 v1
  = coe du_subtraction'45'leq'45'ℕ_376 (coe v0) (coe v1)
-- elementary-number-theory.inequality-natural-numbers.leq-subtraction-ℕ
d_leq'45'subtraction'45'ℕ_402 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_leq'45'subtraction'45'ℕ_402 = erased
-- elementary-number-theory.inequality-natural-numbers.cases-order-three-elements-ℕ
d_cases'45'order'45'three'45'elements'45'ℕ_424 ::
  Integer -> Integer -> Integer -> ()
d_cases'45'order'45'three'45'elements'45'ℕ_424 = erased
-- elementary-number-theory.inequality-natural-numbers.order-three-elements-ℕ
d_order'45'three'45'elements'45'ℕ_438 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_order'45'three'45'elements'45'ℕ_438 v0 v1 v2
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                       (coe
                          MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                          (coe
                             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                             erased erased)))
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  case coe v2 of
                    0 -> coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                           (coe
                              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                              (coe
                                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                 erased erased))
                    _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                         coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                           (coe
                              MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
                              (coe
                                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                 erased)
                              (coe
                                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                 erased)
                              (coe d_decide'45'leq'45'ℕ_196 (coe v3) (coe v4)))
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> case coe v2 of
                    0 -> coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                           (coe
                              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                              (coe
                                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                                 (coe
                                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                    erased erased)))
                    _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                         coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                           (coe
                              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22
                              (coe
                                 MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
                                 (coe
                                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                    erased)
                                 (coe
                                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                    erased)
                                 (coe d_decide'45'leq'45'ℕ_196 (coe v4) (coe v3))))
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  case coe v2 of
                    0 -> coe
                           MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                           (coe
                              MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                              (coe
                                 MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
                                 (coe
                                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                    erased)
                                 (coe
                                    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                    erased)
                                 (coe d_decide'45'leq'45'ℕ_196 (coe v3) (coe v4))))
                    _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                         coe
                           d_order'45'three'45'elements'45'ℕ_438 (coe v3) (coe v4) (coe v5)
-- elementary-number-theory.inequality-natural-numbers.le-ℕ
d_le'45'ℕ_464 :: Integer -> Integer -> ()
d_le'45'ℕ_464 = erased
-- elementary-number-theory.inequality-natural-numbers._<_
d__'60'__474 :: Integer -> Integer -> ()
d__'60'__474 = erased
-- elementary-number-theory.inequality-natural-numbers.anti-reflexive-le-ℕ
d_anti'45'reflexive'45'le'45'ℕ_478 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_anti'45'reflexive'45'le'45'ℕ_478 = erased
-- elementary-number-theory.inequality-natural-numbers.transitive-le-ℕ
d_transitive'45'le'45'ℕ_488 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_transitive'45'le'45'ℕ_488 = erased
-- elementary-number-theory.inequality-natural-numbers.contradiction-le-zero-ℕ
d_contradiction'45'le'45'zero'45'ℕ_510 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_contradiction'45'le'45'zero'45'ℕ_510 = erased
-- elementary-number-theory.inequality-natural-numbers.contradiction-le-one-ℕ
d_contradiction'45'le'45'one'45'ℕ_516 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_contradiction'45'le'45'one'45'ℕ_516 = erased
-- elementary-number-theory.inequality-natural-numbers.transitive-le-ℕ'
d_transitive'45'le'45'ℕ''_526 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_transitive'45'le'45'ℕ''_526 = erased
-- elementary-number-theory.inequality-natural-numbers.succ-le-ℕ
d_succ'45'le'45'ℕ_568 :: Integer -> AgdaAny
d_succ'45'le'45'ℕ_568 = erased
-- elementary-number-theory.inequality-natural-numbers.preserves-le-succ-ℕ
d_preserves'45'le'45'succ'45'ℕ_576 ::
  Integer -> Integer -> AgdaAny -> AgdaAny
d_preserves'45'le'45'succ'45'ℕ_576 = erased
-- elementary-number-theory.inequality-natural-numbers.anti-symmetric-le-ℕ
d_anti'45'symmetric'45'le'45'ℕ_588 ::
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_anti'45'symmetric'45'le'45'ℕ_588 = erased
-- elementary-number-theory.inequality-natural-numbers.is-decidable-le-ℕ
d_is'45'decidable'45'le'45'ℕ_602 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'le'45'ℕ_602 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe (\ v2 -> v2))
             _ -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe (\ v3 -> v3))
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe d_is'45'decidable'45'le'45'ℕ_602 (coe v2) (coe v3)
-- elementary-number-theory.inequality-natural-numbers.contradiction-le-ℕ
d_contradiction'45'le'45'ℕ_616 ::
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_contradiction'45'le'45'ℕ_616 = erased
-- elementary-number-theory.inequality-natural-numbers.contradiction-le-ℕ'
d_contradiction'45'le'45'ℕ''_634 ::
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_contradiction'45'le'45'ℕ''_634 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-not-le-ℕ
d_leq'45'not'45'le'45'ℕ_648 ::
  Integer ->
  Integer ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_leq'45'not'45'le'45'ℕ_648 = erased
-- elementary-number-theory.inequality-natural-numbers.is-nonzero-le-ℕ
d_is'45'nonzero'45'le'45'ℕ_670 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'le'45'ℕ_670 = erased
-- elementary-number-theory.inequality-natural-numbers.contradiction-leq-ℕ
d_contradiction'45'leq'45'ℕ_684 ::
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_contradiction'45'leq'45'ℕ_684 = erased
-- elementary-number-theory.inequality-natural-numbers.contradiction-leq-ℕ'
d_contradiction'45'leq'45'ℕ''_698 ::
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_contradiction'45'leq'45'ℕ''_698 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-le-ℕ
d_leq'45'le'45'ℕ_712 :: Integer -> Integer -> AgdaAny -> AgdaAny
d_leq'45'le'45'ℕ_712 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-le-succ-ℕ
d_leq'45'le'45'succ'45'ℕ_728 ::
  Integer -> Integer -> AgdaAny -> AgdaAny
d_leq'45'le'45'succ'45'ℕ_728 = erased
-- elementary-number-theory.inequality-natural-numbers.concatenate-leq-le-ℕ
d_concatenate'45'leq'45'le'45'ℕ_746 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_concatenate'45'leq'45'le'45'ℕ_746 = erased
-- elementary-number-theory.inequality-natural-numbers.concatenate-le-leq-ℕ
d_concatenate'45'le'45'leq'45'ℕ_778 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_concatenate'45'le'45'leq'45'ℕ_778 = erased
-- elementary-number-theory.inequality-natural-numbers.concatenate-eq-le-eq-ℕ
d_concatenate'45'eq'45'le'45'eq'45'ℕ_806 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_concatenate'45'eq'45'le'45'eq'45'ℕ_806 = erased
-- elementary-number-theory.inequality-natural-numbers.concatenate-eq-le-ℕ
d_concatenate'45'eq'45'le'45'ℕ_816 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny -> AgdaAny
d_concatenate'45'eq'45'le'45'ℕ_816 = erased
-- elementary-number-theory.inequality-natural-numbers.concatenate-le-eq-ℕ
d_concatenate'45'le'45'eq'45'ℕ_826 ::
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_concatenate'45'le'45'eq'45'ℕ_826 = erased
-- elementary-number-theory.inequality-natural-numbers.le-succ-ℕ
d_le'45'succ'45'ℕ_832 :: Integer -> AgdaAny
d_le'45'succ'45'ℕ_832 = erased
-- elementary-number-theory.inequality-natural-numbers.le-leq-neq-ℕ
d_le'45'leq'45'neq'45'ℕ_840 ::
  Integer ->
  Integer ->
  AgdaAny ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_le'45'leq'45'neq'45'ℕ_840 = erased
-- elementary-number-theory.inequality-natural-numbers.linear-le-ℕ
d_linear'45'le'45'ℕ_866 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_linear'45'le'45'ℕ_866 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased)
             _ -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                    (coe MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased)
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
                    (coe (\ v4 -> v4))
                    (coe
                       MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
                       erased (coe (\ v4 -> v4)))
                    (coe d_linear'45'le'45'ℕ_866 (coe v2) (coe v3))
-- elementary-number-theory.inequality-natural-numbers.le-is-nonzero-ℕ
d_le'45'is'45'nonzero'45'ℕ_878 ::
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_le'45'is'45'nonzero'45'ℕ_878 = erased
-- elementary-number-theory.inequality-natural-numbers.subtraction-le-ℕ
d_subtraction'45'le'45'ℕ_892 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_subtraction'45'le'45'ℕ_892 v0 v1 ~v2
  = du_subtraction'45'le'45'ℕ_892 v0 v1
du_subtraction'45'le'45'ℕ_892 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_subtraction'45'le'45'ℕ_892 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
             (coe v1)
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                erased erased)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                (coe du_P_910 (coe v2) (coe v3)))
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                   (coe
                      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                      (coe du_P_910 (coe v2) (coe v3))))
                erased)
-- elementary-number-theory.inequality-natural-numbers._.P
d_P_910 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_P_910 v0 v1 ~v2 = du_P_910 v0 v1
du_P_910 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_P_910 v0 v1
  = coe du_subtraction'45'le'45'ℕ_892 (coe v0) (coe v1)
-- elementary-number-theory.inequality-natural-numbers.le-subtraction-ℕ
d_le'45'subtraction'45'ℕ_918 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_le'45'subtraction'45'ℕ_918 = erased
-- elementary-number-theory.inequality-natural-numbers.left-law-leq-add-ℕ
d_left'45'law'45'leq'45'add'45'ℕ_946 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_left'45'law'45'leq'45'add'45'ℕ_946 = erased
-- elementary-number-theory.inequality-natural-numbers.right-law-leq-add-ℕ
d_right'45'law'45'leq'45'add'45'ℕ_966 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_right'45'law'45'leq'45'add'45'ℕ_966 = erased
-- elementary-number-theory.inequality-natural-numbers.preserves-leq-add-ℕ
d_preserves'45'leq'45'add'45'ℕ_984 ::
  Integer ->
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_preserves'45'leq'45'add'45'ℕ_984 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-add-ℕ
d_leq'45'add'45'ℕ_1002 :: Integer -> Integer -> AgdaAny
d_leq'45'add'45'ℕ_1002 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-add-ℕ'
d_leq'45'add'45'ℕ''_1014 :: Integer -> Integer -> AgdaAny
d_leq'45'add'45'ℕ''_1014 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-leq-add-ℕ
d_leq'45'leq'45'add'45'ℕ_1026 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_leq'45'leq'45'add'45'ℕ_1026 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-leq-add-ℕ'
d_leq'45'leq'45'add'45'ℕ''_1048 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_leq'45'leq'45'add'45'ℕ''_1048 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-leq-mul-ℕ
d_leq'45'leq'45'mul'45'ℕ_1064 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_leq'45'leq'45'mul'45'ℕ_1064 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-leq-mul-ℕ'
d_leq'45'leq'45'mul'45'ℕ''_1096 ::
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_leq'45'leq'45'mul'45'ℕ''_1096 = erased
-- elementary-number-theory.inequality-natural-numbers.neq-le-ℕ
d_neq'45'le'45'ℕ_1110 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_neq'45'le'45'ℕ_1110 = erased
-- elementary-number-theory.inequality-natural-numbers.is-prop-leq-ℕ
d_is'45'prop'45'leq'45'ℕ_1128 ::
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'leq'45'ℕ_1128 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_is'45'prop'45'unit_82)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> \ v3 ->
                    coe
                      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe d_is'45'prop'45'leq'45'ℕ_1128 (coe v2) (coe v3)
-- elementary-number-theory.inequality-natural-numbers.leq-ℕ-Prop
d_leq'45'ℕ'45'Prop_1138 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_leq'45'ℕ'45'Prop_1138 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'prop'45'leq'45'ℕ_1128 (coe v0) (coe v1))
-- elementary-number-theory.inequality-natural-numbers.neg-succ-leq-ℕ
d_neg'45'succ'45'leq'45'ℕ_1150 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_neg'45'succ'45'leq'45'ℕ_1150 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-eq-left-ℕ
d_leq'45'eq'45'left'45'ℕ_1160 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  Integer -> AgdaAny -> AgdaAny
d_leq'45'eq'45'left'45'ℕ_1160 = erased
-- elementary-number-theory.inequality-natural-numbers.leq-eq-right-ℕ
d_leq'45'eq'45'right'45'ℕ_1170 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny -> AgdaAny
d_leq'45'eq'45'right'45'ℕ_1170 = erased
-- elementary-number-theory.inequality-natural-numbers.cases-leq-succ-ℕ
d_cases'45'leq'45'succ'45'ℕ_1178 ::
  Integer ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_cases'45'leq'45'succ'45'ℕ_1178 v0 v1 ~v2
  = du_cases'45'leq'45'succ'45'ℕ_1178 v0 v1
du_cases'45'leq'45'succ'45'ℕ_1178 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_cases'45'leq'45'succ'45'ℕ_1178 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 erased
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             0 -> coe
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 erased
             _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
                    (coe (\ v4 -> v4)) erased
                    (coe du_cases'45'leq'45'succ'45'ℕ_1178 (coe v2) (coe v3))
